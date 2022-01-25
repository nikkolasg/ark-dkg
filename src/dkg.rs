use crate::eval_native::PolyEvaluator;
use ark_crypto_primitives::{snark::SNARKGadget, SNARK};
use ark_ec::PairingEngine;
use ark_groth16::{constraints::Groth16VerifierGadget, Groth16};
use ark_groth16::{PreparedVerifyingKey, Proof as GrothProof, ProvingKey};
use ark_r1cs_std::pairing::PairingVar;
use ark_r1cs_std::prelude::*;
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::marker::PhantomData;
use ark_std::rand::{CryptoRng, Rng};
use ark_std::UniformRand;

pub struct DKGConfig<I: PairingEngine> {
    secret: I::Fr,
    threshold: usize,
    ids: Vec<I::Fr>,
    inner_pk: ProvingKey<I>,
    inner_vk: PreparedVerifyingKey<I>,
}

pub struct DKGCircuit<O, I, IV>
where
    O: PairingEngine,
    I: PairingEngine<Fq = O::Fr>,
    IV: PairingVar<I>,
{
    conf: DKGConfig<I>,
    pub_inputs: Vec<I::Fr>,
    inner_proof: GrothProof<I>,
    _op: PhantomData<O>,
    _ip: PhantomData<IV>,
}

impl<O, I, IV> DKGCircuit<O, I, IV>
where
    O: PairingEngine,
    I: PairingEngine<Fq = O::Fr>,
    IV: PairingVar<I>,
{
    pub fn new<R: Rng + CryptoRng>(
        conf: DKGConfig<I>,
        mut rng: &mut R,
    ) -> Result<Self, SynthesisError> {
        // -2 because -1 for the first coefficient which is the secret and -1
        // because threshold is the number of evaluation pairs you need to
        // reconstruct the poly, so it's the degree of the polynomial +1
        // Therefore we want the degree to be threshold -1
        let coeffs = std::iter::once(conf.secret)
            .chain((0..conf.threshold - 2).map(|_| I::Fr::rand(&mut rng)))
            .collect::<Vec<_>>();
        let pe = PolyEvaluator::<I::Fr>::new(coeffs, conf.ids.clone());
        let pub_inputs = pe.public_inputs();
        let proof = Groth16::<I>::prove(&conf.inner_pk, pe, &mut rng)?;
        Ok(Self {
            conf: conf,
            inner_proof: proof,
            pub_inputs: pub_inputs,
            _op: PhantomData,
            _ip: PhantomData,
        })
    }

    pub fn check_evaluation_proof(
        self,
        cs: ConstraintSystemRef<O::Fr>,
    ) -> Result<(), SynthesisError> {
        println!("verifying native proof");
        assert!(ark_groth16::verify_proof(
            &self.conf.inner_vk,
            &self.inner_proof,
            &self.pub_inputs
        )
        .unwrap());
        println!("verifying native proof PASSED");
        // prepare inputs, proof and vk vars
        let inputs_var =
            <Groth16VerifierGadget<I, IV> as SNARKGadget<
                <I as PairingEngine>::Fr,
                <I as PairingEngine>::Fq,
                Groth16<I>,
            >>::InputVar::new_input(ns!(cs, "inner inputs"), || Ok(self.pub_inputs))?;
        let proof_var =
            <Groth16VerifierGadget<I, IV> as SNARKGadget<
                <I as PairingEngine>::Fr,
                <I as PairingEngine>::Fq,
                Groth16<I>,
            >>::ProofVar::new_witness(ns!(cs, "inner proof"), || Ok(self.inner_proof))?;
        let vk_var = <Groth16VerifierGadget<I, IV> as SNARKGadget<
            <I as PairingEngine>::Fr,
            <I as PairingEngine>::Fq,
            Groth16<I>,
        >>::ProcessedVerifyingKeyVar::new_witness(
            ns!(cs, "inner vk"), || Ok(self.conf.inner_vk)
        )?;
        Groth16VerifierGadget::<I, IV>::verify_with_processed_vk(&vk_var, &inputs_var, &proof_var)?
            .enforce_equal(&Boolean::constant(true))?;
        Ok(())
    }
}
impl<O, I, IV> ConstraintSynthesizer<O::Fr> for DKGCircuit<O, I, IV>
where
    O: PairingEngine,
    I: PairingEngine<Fq = O::Fr>,
    IV: PairingVar<I>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<O::Fr>) -> Result<(), SynthesisError> {
        self.check_evaluation_proof(cs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_377::{constraints::PairingVar as IV, Bls12_377 as I, Fr};
    use ark_bw6_761::BW6_761 as O;
    use ark_ec::ProjectiveCurve;
    use ark_groth16::Groth16;
    use ark_relations::r1cs::{ConstraintLayer, ConstraintSystem, TracingMode};
    use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_std::UniformRand;
    use ark_std::Zero;
    use tracing_subscriber::layer::SubscriberExt;

    #[test]
    fn dkg() {
        let mut rng = ark_std::test_rng();
        let threshold = 3;
        let degree = threshold - 1;
        let n = degree * 2;
        let secret = Fr::rand(&mut rng);
        let ids = (0..n).map(|i| Fr::from((i + 1) as u32)).collect::<Vec<_>>();
        // create pk, vk for inner proof
        let (pk, vk) = {
            let coeffs = std::iter::once(secret.clone())
                .chain((0..threshold - 2).map(|_| Fr::rand(&mut rng)))
                .collect::<Vec<_>>();
            let pe = PolyEvaluator::<Fr>::new(coeffs, ids.clone());
            Groth16::setup(pe, &mut rng).unwrap()
        };
        let pvk = Groth16::<I>::process_vk(&vk).unwrap();

        //
        let config = DKGConfig {
            secret: secret,
            threshold: threshold,
            ids: ids,
            inner_pk: pk,
            inner_vk: pvk,
        };
        let circuit = DKGCircuit::<O, I, IV>::new(config, &mut rng).unwrap();

        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);
        let cs = ConstraintSystem::<<O as PairingEngine>::Fr>::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();
        println!("Num constraints: {}", cs.num_constraints());
        assert!(
            cs.is_satisfied().unwrap(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap().unwrap_or_default()
        );
    }
}
