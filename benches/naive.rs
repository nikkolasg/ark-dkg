#![feature(int_log)]
use ark_bls12_377::{constraints::PairingVar as IV, Bls12_377 as I};
use ark_bw6_761::BW6_761 as O;
use ark_crypto_primitives::snark::BooleanInputVar;
use ark_crypto_primitives::snark::SNARKGadget;
use ark_ec::PairingEngine;
use ark_groth16::constraints::Groth16VerifierGadget;
use ark_groth16::Proof as GrothProof;
use ark_groth16::{Groth16, PreparedVerifyingKey};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::prelude::PairingVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_relations::{lc, ns};
use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_std::UniformRand;
use eyre::Result;
use std::marker::PhantomData;
use std::ops::MulAssign;
use serde::Serialize;

struct InnerGroth16<I: PairingEngine> {
    a: Option<I::Fr>,
    b: Option<I::Fr>,
    nconstraint: u64,
    _p: PhantomData<I>,
}

impl<I: PairingEngine> InnerGroth16<I> {
    fn new(nconstraint: u64) -> Self {
        let a = I::Fr::rand(&mut rand::thread_rng());
        let b = I::Fr::rand(&mut rand::thread_rng());
        Self {
            a: Some(a),
            b: Some(b),
            nconstraint,
            _p: PhantomData,
        }
    }
}

impl<I: PairingEngine> ConstraintSynthesizer<I::Fr> for InnerGroth16<I> {
    fn generate_constraints(self, cs: ConstraintSystemRef<I::Fr>) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_witness_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
            a.mul_assign(&b);
            Ok(a)
        })?;
        for _ in 0..self.nconstraint {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
struct OuterConfig<I: PairingEngine, IV: PairingVar<I>> {
    inner_proof: GrothProof<I>,
    inner_pvk: PreparedVerifyingKey<I>,
    _p: PhantomData<IV>,
}

struct OuterGroth16<I: PairingEngine, IV: PairingVar<I>> {
    inner_proof: GrothProof<I>,
    inner_pvk: PreparedVerifyingKey<I>,
    _p: PhantomData<IV>,
}

impl<I: PairingEngine, IV: PairingVar<I>> OuterGroth16<I, IV> {
    fn new(c: OuterConfig<I, IV>) -> Result<Self> {
        Ok(Self {
            inner_proof: c.inner_proof,
            inner_pvk: c.inner_pvk,
            _p: PhantomData,
        })
    }
}

impl<I, IV> ConstraintSynthesizer<I::Fq> for OuterGroth16<I, IV>
where
    I: PairingEngine,
    IV: PairingVar<I>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<I::Fq>) -> Result<(), SynthesisError> {
        let inputs_var = BooleanInputVar::<I::Fr, I::Fq>::new(Vec::new());
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
            ns!(cs, "inner vk"), || Ok(self.inner_pvk)
        )?;
        Groth16VerifierGadget::<I, IV>::verify_with_processed_vk(&vk_var, &inputs_var, &proof_var)?
            .enforce_equal(&Boolean::constant(true))?;
        Ok(())
    }
}
#[derive(Default, Clone, Debug, Serialize)]
struct BenchResult {
    inner_constraints: u32,
    inner_setup_time: u128,
    inner_proof_time: u128,
    outer_setup_time: u128,
    proving_time: u128,
    verification_time: u128,
}

use std::time::Instant;

fn main() -> Result<()> {
    let sizes = vec![1<<8, 1<<10];
    let mut writer = csv::Writer::from_path("naive.csv").expect("unable to open csv writer");
    for n in sizes { 
        let power2 = (n as u64).ilog2();
        println!("[+] Starting benchmark with n=2^{}",power2);

        print!("\t- Generating setup for inner proof");
        let now = Instant::now();
        let (inner_pk, inner_vk) =
            Groth16::setup(InnerGroth16::<I>::new(n), &mut rand::thread_rng()).unwrap();
        let inner_pvk = Groth16::<I>::process_vk(&inner_vk)?;
        let inner_setup_time = now.elapsed().as_millis();
        println!(" \t\t-> took {} ms",inner_setup_time);

        print!("\t- Generating inner proof");
        let now = Instant::now();
        let inner_proof = Groth16::<I>::prove(
            &inner_pk,
            InnerGroth16::<I>::new(n),
            &mut rand::thread_rng(),
        )?;
        let inner_proof_time = now.elapsed().as_millis();
        println!(" \t\t\t-> took {} ms",inner_proof_time);


        print!("\t- Generating setup for outer proof");
        let now = Instant::now();
        let outer_config = OuterConfig::<I, IV> {
            inner_proof: inner_proof.clone(),
            inner_pvk: inner_pvk.clone(),
            _p: PhantomData,
        };
        let (outer_pk, outer_vk) =
            Groth16::setup(OuterGroth16::new(outer_config)?, &mut rand::thread_rng()).unwrap();
        let outer_pvk = Groth16::<O>::process_vk(&outer_vk)?;
        let outer_setup_time = now.elapsed().as_millis();
        println!(" \t\t-> took {} ms",outer_setup_time);

    
        print!("\t- Generating full proof");
        let now = Instant::now();
        let outer_config = OuterConfig::<I, IV> {
            inner_proof: inner_proof,
            inner_pvk: inner_pvk.clone(),
            _p: PhantomData,
        };
    
        let proof = Groth16::<O>::prove(
            &outer_pk,
            OuterGroth16::new(outer_config)?,
            &mut rand::thread_rng(),
        )
        .unwrap();
        let proving_time = now.elapsed().as_millis();
        println!(" \t\t\t-> took {} ms",proving_time);
 
        print!("\t- Running verifier");
        let now = Instant::now();
        let valid = ark_groth16::verify_proof(&outer_pvk, &proof, &vec![]).unwrap();
        assert!(valid, "proof is not valid");
        let verification_time = now.elapsed().as_millis();
        println!(" \t\t\t\t-> took {} ms",verification_time);
        writer.serialize(BenchResult {
            inner_constraints: power2,
            inner_proof_time,
            inner_setup_time,
            outer_setup_time,
            proving_time,
            verification_time, 
        }).expect("could not write to csv");
        writer.flush().expect("could not flush");
    }
    Ok(())
}
