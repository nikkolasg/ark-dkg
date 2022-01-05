use ark_bls12_377::{
    constraints::{G1Var, G2Var, PairingVar as Bls12_377PairingGadget},
    Bls12_377, Fr as Bls12_377Fr, G1Projective, G2Projective,
};
use ark_bw6_761::Fr as BW6_761Fr;
use ark_ec::PairingEngine;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

#[derive(Clone)]
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
    use ark_bw6_761::BW6_761 as P;
    use ark_ec::ProjectiveCurve;
    use ark_groth16::Groth16;
    use ark_snark::SNARK;

    #[test]
    fn poly() {
        let circuit = PolyCircuit::<BF> {
            p1: <BF as PairingEngine>::G1Projective::prime_subgroup_generator(),
        };
        let mut rng = ark_std::test_rng();
        let (pk, vk) = Groth16::<P>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
        let proof = Groth16::prove(&pk, circuit.clone(), &mut rng).unwrap();
        let valid_proof = Groth16::verify(&vk, &vec![], &proof).unwrap();
        assert!(valid_proof);
    }
}
