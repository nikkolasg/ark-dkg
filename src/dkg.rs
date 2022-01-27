use crate::encrypt::EncryptCircuit;
use crate::eval_native::PolyEvaluator;
use crate::feldman::CommitCircuit;
use ark_crypto_primitives::snark::SNARKGadget;
use ark_crypto_primitives::snark::{BooleanInputVar, SNARK};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{BitIteratorLE, PrimeField};
use ark_groth16::{constraints::Groth16VerifierGadget, Groth16};
use ark_groth16::{PreparedVerifyingKey, Proof as GrothProof, ProvingKey};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::pairing::PairingVar;
use ark_r1cs_std::prelude::*;
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::AbsorbGadget;
use ark_sponge::{poseidon::PoseidonParameters, Absorb};
use ark_std::marker::PhantomData;
use ark_std::ops::MulAssign;
use ark_std::rand::{CryptoRng, Rng};
use ark_std::vec::Vec;
use ark_std::UniformRand;
use rayon::prelude::*;

pub struct Node<C: ProjectiveCurve> {
    pub key: C,
    pub idx: C::ScalarField,
}

pub struct DKGConfig<I: PairingEngine> {
    secret: I::Fr,
    threshold: usize,
    // indices to be attributed to each public keys
    participants: Vec<Node<I::G1Projective>>,
    inner_pk: ProvingKey<I>,
    inner_vk: PreparedVerifyingKey<I>,
    poseidon_params: PoseidonParameters<I::Fq>,
}

impl<I> DKGConfig<I>
where
    I: PairingEngine,
{
    pub fn ids(&self) -> Vec<I::Fr> {
        self.participants.par_iter().map(|p| p.idx).collect()
    }
    pub fn public_keys(&self) -> Vec<I::G1Projective> {
        self.participants.par_iter().map(|p| p.key).collect()
    }
}

pub struct DKGCircuit<I, IV>
where
    I: PairingEngine,
    IV: PairingVar<I>,
    // mimicking encrypt restriction on types
    I::Fq: PrimeField,
    //// TODO Why is this not taken into account ?
    IV::G1Var: AbsorbGadget<I::Fq>,
    I::G1Affine: Absorb,
{
    conf: DKGConfig<I>,
    inner_proof: GrothProof<I>,
    commitments: Vec<I::G1Projective>,
    coeffs: Vec<I::Fr>,
    shares: Vec<I::Fr>,
    encryption: EncryptCircuit<I::G1Projective, IV::G1Var>,
    //_op: PhantomData<O>,
    _ip: PhantomData<IV>,
}

impl<I, IV> DKGCircuit<I, IV>
where
    //O: PairingEngine,
    I: PairingEngine,
    //IV: PairingVar<I, <O as PairingEngine>::Fr>,
    IV: PairingVar<I>,
    I::Fq: PrimeField,
    IV::G1Var: AbsorbGadget<I::Fq>,
    I::G1Affine: Absorb,
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
        let pe = PolyEvaluator::<I::Fr>::new(coeffs.clone(), conf.ids());
        // TODO make that generator an input
        let shares = pe.evaluation_results();

        let commitments = shares
            .par_iter()
            .cloned()
            .map(|s| {
                let mut c = I::G1Projective::prime_subgroup_generator();
                c.mul_assign(s);
                c
            })
            .collect::<Vec<_>>();
        // evaluation proof of the shares
        let proof = Groth16::<I>::prove(&conf.inner_pk, pe, &mut rng)?;
        // encryption gadget
        let encryption = EncryptCircuit::<I::G1Projective, IV::G1Var>::new(
            shares.clone(),
            conf.public_keys(),
            conf.poseidon_params.clone(),
            &mut rng,
        );

        Ok(Self {
            conf: conf,
            inner_proof: proof,
            coeffs: coeffs,
            shares: shares,
            commitments: commitments,
            encryption: encryption,
            //_op: PhantomData,
            _ip: PhantomData,
        })
    }

    pub fn check_evaluation_proof(
        self,
        cs: ConstraintSystemRef<I::Fq>,
        shares: &[Vec<Boolean<I::Fq>>],
    ) -> Result<(), SynthesisError> {
        println!("verifying native proof");

        debug_assert!({
            let mut pub_inputs = self.coeffs.clone();
            pub_inputs.extend(self.conf.ids());
            pub_inputs.extend(self.shares.clone());
            ark_groth16::verify_proof(&self.conf.inner_vk, &self.inner_proof, &pub_inputs).unwrap()
        });
        println!("verifying native proof PASSED");
        // the inputs are : coefficients, evaluations points and results
        // (shares)
        let share_bits = self
            .shares
            .iter()
            .map(|s| {
                let bits: Vec<bool> = BitIteratorLE::new(s.into_repr().as_ref().to_vec()).collect();
                Vec::new_witness(ark_relations::ns!(cs, "shares"), || Ok(bits))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let coeffs_bits = self
            .coeffs
            .iter()
            .map(|c| {
                let bits: Vec<bool> = BitIteratorLE::new(c.into_repr().as_ref().to_vec()).collect();
                Vec::new_witness(ark_relations::ns!(cs, "shares"), || Ok(bits))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ids_bits = self
            .conf
            .ids()
            .iter()
            .map(|i| {
                let bits: Vec<bool> = BitIteratorLE::new(i.into_repr().as_ref().to_vec()).collect();
                Vec::new_input(ark_relations::ns!(cs, "shares"), || Ok(bits))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut pub_inputs = coeffs_bits;
        pub_inputs.extend(ids_bits);
        pub_inputs.extend(share_bits);
        // TODO - provide ways to do that easily
        let inputs_var = BooleanInputVar::<I::Fr, I::Fq>::new(pub_inputs);

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

    fn verify_feldman_commitments(
        &self,
        cs: ConstraintSystemRef<I::Fq>,
        shares: &[Vec<Boolean<I::Fq>>],
        gen: &IV::G1Var,
    ) -> Result<(), SynthesisError> {
        let commitment_var = self
            .commitments
            .iter()
            .map(|coeff| {
                // TODO should probably put back subgroup check
                IV::G1Var::new_variable_omit_prime_order_check(
                    ark_relations::ns!(cs, "generate_p1"),
                    || Ok(coeff.clone()),
                    AllocationMode::Input,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (comm, share) in commitment_var.iter().zip(shares.iter()) {
            let exp = gen.scalar_mul_le(share.iter())?;
            comm.enforce_equal(&exp)?;
        }
        /*        {*/
        //I::G1Projective::prime_subgroup_generator()
        //.into_affine()
        //.xy();
        //IV::G1Var::new_variable(
        //ark_relations::ns!(cs, "generate_p1"),
        //|| Ok(I::G1Affine::prime_subgroup_generator()),
        //AllocationMode::Input,
        //)
        //.unwrap()
        //.affine_coords()
        //.unwrap();
        //()
        /*}*/
        Ok(())
    }
}
impl<I, IV> ConstraintSynthesizer<I::Fq> for DKGCircuit<I, IV>
where
    //I: PairingEngine<Fq = O::Fr>,
    //IV: PairingVar<I, <O as PairingEngine>::Fr>,
    I: PairingEngine,
    IV: PairingVar<I>,
    IV::G1Var: AbsorbGadget<I::Fq>,
    I::G1Affine: Absorb,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<I::Fq>) -> Result<(), SynthesisError> {
        // shares are commin input between the Groth16 verification circuit and
        // the commitment circuit evaluation so we need to create the var once
        // and give that to both subcomponents - the API for Groth16 doesn't
        // allow us that so we need to create BooleanInputVar directly
        // ASSUMPTIONS: I::Fr < I::Fq which is true for bls12-377
        // We are taking the shares as witness in FpVar and turning them into Vec<Boolean<I::Fq>>
        let share_fields = self
            .shares
            .iter()
            .map(|s| {
                NonNativeFieldVar::<I::Fr, I::Fq>::new_witness(
                    ark_relations::ns!(cs, "share_nonnative"),
                    || Ok(s),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let share_bits = share_fields
            //self.shares
            .iter()
            .map(|s| {
                //let bits: Vec<bool> = BitIteratorLE::new(s.into_repr().as_ref().to_vec()).collect();
                //Vec::new_witness(ark_relations::ns!(cs, "shares"), || Ok(bits))
                s.to_bits_le()
            })
            .collect::<Result<Vec<_>, _>>()?;

        // generator variable
        let g = IV::G1Var::new_variable_omit_prime_order_check(
            ark_relations::ns!(cs, "generator"),
            || Ok(I::G1Projective::prime_subgroup_generator()),
            AllocationMode::Input,
        )?;

        // we then give the same shares to both
        self.verify_feldman_commitments(cs.clone(), &share_bits, &g)?;
        self.encryption
            .verify_encryption(cs.clone(), &share_fields)?;
        self.check_evaluation_proof(cs.clone(), &share_bits)?;
        Ok(())
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
        let participants = (0..n)
            .map(
                |i| <I as PairingEngine>::G1Projective::rand(&mut rng), // dont care for the moment
            )
            .zip(ids.iter())
            .map(|(p, idx)| Node {
                idx: idx.clone(),
                key: p,
            })
            .collect::<Vec<_>>();
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
            participants: participants,
            inner_pk: pk,
            inner_vk: pvk,
            poseidon_params: crate::poseidon::get_bls12377_fq_params(2),
        };
        let circuit = DKGCircuit::<I, IV>::new(config, &mut rng).unwrap();

        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);
        let cs = ConstraintSystem::<<I as PairingEngine>::Fq>::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();
        println!("Num constraints: {}", cs.num_constraints());
        assert!(
            cs.is_satisfied().unwrap(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap().unwrap_or_default()
        );
    }
}
