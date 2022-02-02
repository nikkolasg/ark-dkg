use crate::encrypt::EncryptCircuit;
use crate::eval_native::PolyCircuit;
use ark_crypto_primitives::snark::SNARKGadget;
use ark_crypto_primitives::snark::{BooleanInputVar, SNARK};
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::{BigInteger, BitIteratorLE, PrimeField};
use ark_groth16::{constraints::Groth16VerifierGadget, Groth16};
use ark_groth16::{PreparedVerifyingKey, Proof as GrothProof, ProvingKey};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::pairing::PairingVar;
use ark_r1cs_std::prelude::*;
use ark_relations::ns;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::{AbsorbGadget, CryptographicSpongeVar};
use ark_sponge::{poseidon::PoseidonParameters, Absorb};
use ark_sponge::{
    poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
    CryptographicSponge,
};
use ark_std::marker::PhantomData;
use ark_std::ops::MulAssign;
use ark_std::rand::{CryptoRng, Rng};
use ark_std::vec::Vec;
use ark_std::UniformRand;
use rayon::prelude::*;

#[derive(Clone)]
pub struct Node<C: ProjectiveCurve> {
    pub key: C,
    pub idx: C::ScalarField,
}

#[derive(Clone)]
pub struct DKGConfig<I: PairingEngine> {
    pub secret: I::Fr,
    pub threshold: usize,
    // indices to be attributed to each public keys
    pub participants: Vec<Node<I::G1Projective>>,
    pub inner_pk: ProvingKey<I>,
    pub inner_vk: PreparedVerifyingKey<I>,
    pub poseidon_params: PoseidonParameters<I::Fq>,
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
    I::Fq: PrimeField + Absorb,
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
    I::Fq: PrimeField + Absorb,
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
        let pe = PolyCircuit::<I::Fr>::new(coeffs.clone(), conf.ids());
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

    // commitment to the inputs: coeffs,shares,ids
    pub fn input_commitment(&self) -> I::Fq {
        let mut sponge = PoseidonSponge::new(&self.conf.poseidon_params);
        for c in self.commitments.iter() {
            sponge.absorb(&c.into_affine());
        }
        /*println!(*/
            //"native: after Commit {:?}",
            //sponge.squeeze_field_elements::<I::Fq>(1).remove(0)
        /*)*/;

        // assertion is more complex than that but for PoC purpose we'll keep
        // like that. We want to do like in
        // primitive_constraints/snark/constraints style where they decide if a
        // element can be constraints in the other one.
        assert!(I::Fr::size_in_bits() <= I::Fq::size_in_bits());
        for e in self.shares.iter().chain(self.conf.ids().iter()) {
            let scalar_in_fq = &I::Fq::from_repr(<I::Fq as PrimeField>::BigInt::from_bits_le(
                &e.into_repr().to_bits_le(),
            ))
            .unwrap(); // because Fr < Fq

            //let bits = &e.into_repr().to_bits_le();
            sponge.absorb(&scalar_in_fq);
        }
        /*println!(*/
        //"native: after Fr {:?}",
        //sponge.squeeze_field_elements::<I::Fq>(1).remove(0)
        //);

        sponge.squeeze_field_elements(1).remove(0)
    }

    pub fn check_inputs(
        &self,
        cs: ConstraintSystemRef<I::Fq>,
        shares: &[Vec<Boolean<I::Fq>>],
        coeffs_commit: &[IV::G1Var],
        ids: &[Vec<Boolean<I::Fq>>],
    ) -> Result<(), SynthesisError> {
        // input commitment
        let input_var = FpVar::<I::Fq>::new_variable(
            ns!(cs, "input_commitment"),
            || Ok(self.input_commitment()),
            AllocationMode::Input,
        )?;

        let mut poseidon = PoseidonSpongeVar::new(cs.clone(), &self.conf.poseidon_params);
        for c in coeffs_commit.iter() {
            poseidon.absorb(c)?;
        }
        /*if let Ok(v) = poseidon*/
        //.squeeze_field_elements(1)
        //.and_then(|mut v| Ok(v.remove(0)))
        //{
        //println!("Constraint after commit: {:?}", v.value().unwrap());
        /*}*/

        //for e in shares.iter().chain(ids.iter()) {
        for e in self.shares.iter().chain(self.conf.ids().iter()) {
            // TODO why can't we simply use 1 Fq for an Fr
            let scalar_in_fq = &I::Fq::from_repr(<I::Fq as PrimeField>::BigInt::from_bits_le(
                &e.into_repr().to_bits_le(),
            ))
            .unwrap(); // because Fr < Fq

            poseidon.absorb(&FpVar::new_witness(ns!(cs.clone(), "scalar fq"), || {
                Ok(scalar_in_fq)
            })?)?;
        }
        /*if let Ok(v) = poseidon*/
        //.squeeze_field_elements(1)
        //.and_then(|mut v| Ok(v.remove(0)))
        //{
        //println!("Constraint after Fr: {:?}", v.value().unwrap());
        //}

        let exp = poseidon
            .squeeze_field_elements(1)
            .and_then(|mut v| Ok(v.remove(0)))?;
        exp.enforce_equal(&input_var)?;
        Ok(())
    }

    pub fn check_evaluation_proof(
        self,
        cs: ConstraintSystemRef<I::Fq>,
        shares: Vec<Vec<Boolean<I::Fq>>>,
        ids_bits: Vec<Vec<Boolean<I::Fq>>>,
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
        let share_bits = shares; /*self*/
        //.shares
        //.iter()
        //.map(|s| {
        //let bits: Vec<bool> = BitIteratorLE::new(s.into_repr().as_ref().to_vec()).collect();
        //Vec::new_witness(ark_relations::ns!(cs, "shares"), || Ok(bits))
        //})
        /*.collect::<Result<Vec<_>, _>>()?;*/
        let coeffs_bits = self
            .coeffs
            .iter()
            .map(|c| {
                let bits: Vec<bool> = BitIteratorLE::new(c.into_repr().as_ref().to_vec()).collect();
                Vec::new_witness(ark_relations::ns!(cs, "shares"), || Ok(bits))
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
        coeffs_commit: &[IV::G1Var],
        gen: &IV::G1Var,
    ) -> Result<(), SynthesisError> {
        for (comm, share) in coeffs_commit.iter().zip(shares.iter()) {
            let exp = gen.scalar_mul_le(share.iter())?;
            comm.enforce_equal(&exp)?;
        }
        Ok(())
    }
}
impl<I, IV> ConstraintSynthesizer<I::Fq> for DKGCircuit<I, IV>
where
    //I: PairingEngine<Fq = O::Fr>,
    //IV: PairingVar<I, <O as PairingEngine>::Fr>,
    I: PairingEngine,
    IV: PairingVar<I>,
    I::Fq: Absorb,
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
        let ids_bits = self
            .conf
            .ids()
            .iter()
            .map(|i| {
                let bits: Vec<bool> = BitIteratorLE::new(i.into_repr().as_ref().to_vec()).collect();
                Vec::new_witness(ark_relations::ns!(cs, "shares"), || Ok(bits))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // generator variable
        let g = IV::G1Var::new_variable_omit_prime_order_check(
            ark_relations::ns!(cs, "generator"),
            || Ok(I::G1Projective::prime_subgroup_generator()),
            AllocationMode::Witness,
        )?;
        let coeffs_commit = self
            .commitments
            .iter()
            .map(|coeff| {
                // TODO should probably put back subgroup check
                IV::G1Var::new_variable_omit_prime_order_check(
                    ark_relations::ns!(cs, "generate_p1"),
                    || Ok(coeff.clone()),
                    AllocationMode::Witness,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        self.check_inputs(cs.clone(), &share_bits, &coeffs_commit, &ids_bits)?;

        // we then give the same shares to both
        self.verify_feldman_commitments(cs.clone(), &share_bits, &coeffs_commit, &g)?;
        self.encryption
            .verify_encryption(cs.clone(), &share_fields)?;
        self.check_evaluation_proof(cs.clone(), share_bits, ids_bits)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_377::{constraints::PairingVar as IV, Bls12_377 as I, Fr};
    use ark_bw6_761::BW6_761 as O;
    use ark_groth16::Groth16;
    use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_std::UniformRand;

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
                |_| <I as PairingEngine>::G1Projective::rand(&mut rng), // dont care for the moment
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
            let pe = PolyCircuit::<Fr>::new(coeffs, ids.clone());
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
        let circuit = DKGCircuit::<I, IV>::new(config.clone(), &mut rng).unwrap();
        /*let (opk, ovk) = Groth16::setup(circuit, &mut rng).unwrap();*/
        //let opvk = Groth16::<O>::process_vk(&ovk).unwrap();
        //let circuit = DKGCircuit::<I, IV>::new(config, &mut rng).unwrap();
        //let input = vec![circuit.input_commitment()];
        //let oproof = Groth16::<O>::prove(&opk, circuit, &mut rng).unwrap();
        //ark_groth16::verify_proof(&opvk, &oproof, &input).unwrap();

        use ark_relations::r1cs::{ConstraintLayer, ConstraintSystem, TracingMode};
        use tracing_subscriber::layer::SubscriberExt;
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let input = vec![circuit.input_commitment()];
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
