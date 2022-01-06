use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::{BitIteratorLE, PrimeField};
use ark_r1cs_std::pairing::PairingVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::marker::PhantomData;
use ark_std::{vec::Vec, Zero};
use std::ops::MulAssign;

// Goals:
// 0. use pairing based curve BLS12_377 inside circuit and make a SNARK on top
// 1. prove the multiplication a*G
#[derive(Clone)]
pub struct PolyCircuit<E: PairingEngine, P: PairingVar<E>> {
    g: E::G1Projective,  // generator
    p1: E::G1Projective, // public input
    s1: E::Fr,           // private input
    _pairing_gadget: PhantomData<P>,
}

impl<E, P> PolyCircuit<E, P>
where
    E: PairingEngine,
    P: PairingVar<E>,
{
    pub fn new(s: E::Fr) -> Self {
        let g = E::G1Projective::prime_subgroup_generator();
        let mut p = g.clone();
        p.mul_assign(s.clone());
        Self {
            g: g,
            p1: p,
            s1: s,
            _pairing_gadget: PhantomData,
        }
    }
    pub fn empty() -> Self {
        Self {
            g: E::G1Projective::zero(),
            p1: E::G1Projective::zero(),
            s1: E::Fr::zero(),
            _pairing_gadget: PhantomData,
        }
    }
}

impl<E, P> ConstraintSynthesizer<E::Fq> for PolyCircuit<E, P>
where
    E: PairingEngine,
    P: PairingVar<E>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<E::Fq>) -> Result<(), SynthesisError> {
        let g = P::G1Var::new_variable(
            ark_relations::ns!(cs, "generator"),
            || Ok(self.g),
            AllocationMode::Witness,
        )?;
        let p1 = P::G1Var::new_variable(
            ark_relations::ns!(cs, "generate_p1"),
            || Ok(self.p1),
            AllocationMode::Witness,
        )?;

        let s1_bit: Vec<bool> = BitIteratorLE::new(self.s1.into_repr().as_ref().to_vec()).collect();
        let s1_bits = Vec::new_witness(ark_relations::ns!(cs, "s1_bits"), || Ok(s1_bit))?;
        let exp_p1 = g.scalar_mul_le(s1_bits.iter())?;
        p1.enforce_equal(&exp_p1)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_377::{constraints::PairingVar as EV, Bls12_377 as E};
    use ark_bw6_761::BW6_761 as P;
    use ark_ec::ProjectiveCurve;
    use ark_groth16::Groth16;
    use ark_snark::SNARK;
    use ark_std::One;

    #[test]
    fn poly() {
        assert_eq!(
            <E as PairingEngine>::G1Projective::prime_subgroup_generator(),
            <E as PairingEngine>::G1Projective::prime_subgroup_generator(),
        );

        let circuit = PolyCircuit::<E, EV>::new(<E as PairingEngine>::Fr::one());
        let mut rng = ark_std::test_rng();
        let (pk, vk) =
            Groth16::<P>::circuit_specific_setup(PolyCircuit::<E, EV>::empty(), &mut rng).unwrap();
        let proof = Groth16::prove(&pk, circuit, &mut rng).unwrap();
        let valid_proof = Groth16::verify(&vk, &vec![], &proof).unwrap();
        assert!(valid_proof);
    }
}
