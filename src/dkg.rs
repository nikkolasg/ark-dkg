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
    coeffs: Vec<I::Fr>,
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
        let coeffs = std::iter::once(conf.secret)
            .chain((0..conf.threshold - 1).map(|_| I::Fr::rand(&mut rng)))
            .collect::<Vec<_>>();
        let pe = PolyEvaluator::<I::Fr>::new(coeffs.clone(), conf.ids.clone());
        let pub_inputs = pe.public_inputs();
        let proof = Groth16::<I>::prove(&conf.inner_pk, pe, &mut rng)?;
        Ok(Self {
            conf: conf,
            coeffs: coeffs,
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
            >>::ProofVar::new_input(ns!(cs, "inner proof"), || Ok(self.inner_proof))?;
        let vk_var = <Groth16VerifierGadget<I, IV> as SNARKGadget<
            <I as PairingEngine>::Fr,
            <I as PairingEngine>::Fq,
            Groth16<I>,
        >>::ProcessedVerifyingKeyVar::new_input(
            ns!(cs, "inner proof"), || Ok(self.conf.inner_vk)
        )?;
        Groth16VerifierGadget::<I, IV>::verify_with_processed_vk(&vk_var, &inputs_var, &proof_var)?
            .enforce_equal(&Boolean::constant(true))?;
        Ok(())
    }
}
