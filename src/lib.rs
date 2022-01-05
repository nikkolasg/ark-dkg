use ark_bls12_377::{
    constraints::{G1Var, G2Var, PairingVar as Bls12_377PairingGadget},
    Bls12_377, Fr as Bls12_377Fr, G1Projective, G2Projective,
};
use ark_bw6_761::Fr as BW6_761Fr;
use ark_ec::PairingEngine;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

pub struct PolyCircuit<P: PairingEngine> {
    pub p1: P::G1Projective,
}

impl<P> ConstraintSynthesizer<P::Fq> for PolyCircuit<P>
where
    P: PairingEngine,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<P::Fq>) -> Result<(), SynthesisError> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_377::Bls12_377 as BF;
    use ark_ec::ProjectiveCurve;

    #[test]
    fn poly() {
        let p = PolyCircuit::<BF> {
            p1: <BF as PairingEngine>::G1Projective::prime_subgroup_generator(),
        };
    }
}
