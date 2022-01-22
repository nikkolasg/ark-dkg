use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::{BitIteratorLE, PrimeField};
use ark_r1cs_std::pairing::PairingVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::marker::PhantomData;
use ark_std::vec::Vec;
use rayon::prelude::*;
use std::ops::MulAssign;

// Goals:
// 0. use pairing based curve BLS12_377 inside circuit and make a SNARK on top
// 1. prove the multiplication a*G
//
//
// Circuit:
//  * Constraint Field is BW6's scalar field which is equal to BLS12-377 BASE
//  FIELD
//  * Circuit use BLS12-377 basefield and does the poly computation
//  * Some operations are efficient because of using BLS12377 basefield for
//  group operations
#[derive(Clone)]
pub struct FeldmanCommit<E: PairingEngine, P: PairingVar<E>> {
    g: E::G1Projective,         // generator
    pubs: Vec<E::G1Projective>, // public input
    coeffs: Vec<E::Fr>,         // private input
    _pairing_gadget: PhantomData<P>,
}

impl<E, P> FeldmanCommit<E, P>
where
    E: PairingEngine,
    P: PairingVar<E>,
{
    pub fn new(s: Vec<E::Fr>) -> Self {
        let g = E::G1Projective::prime_subgroup_generator();
        let pubs = s
            .par_iter()
            .map(|s| {
                let mut p = g.clone();
                p.mul_assign(s.clone());
                p
            })
            .collect::<Vec<_>>();
        Self {
            g: g,
            pubs,
            coeffs: s,
            _pairing_gadget: PhantomData,
        }
    }
}

impl<E, P> ConstraintSynthesizer<E::Fq> for FeldmanCommit<E, P>
where
    E: PairingEngine,
    P: PairingVar<E>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<E::Fq>) -> Result<(), SynthesisError> {
        let g = P::G1Var::new_variable_omit_prime_order_check(
            ark_relations::ns!(cs, "generator"),
            || Ok(self.g),
            AllocationMode::Input,
        )?;
        let coeffs: Vec<(_, _)> = self
            .pubs
            .into_iter()
            .zip(self.coeffs.iter())
            .map(|(p, s)| {
                let pvar = P::G1Var::new_variable_omit_prime_order_check(
                    ark_relations::ns!(cs, "generate_p1"),
                    || Ok(p),
                    AllocationMode::Input,
                )?;
                let bits: Vec<bool> = BitIteratorLE::new(s.into_repr().as_ref().to_vec()).collect();
                let s_bits = Vec::new_witness(ark_relations::ns!(cs, "s1_bits"), || Ok(bits))?;
                Ok((pvar, s_bits))
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (p, s) in coeffs.iter() {
            let exp = g.scalar_mul_le(s.iter())?;
            p.enforce_equal(&exp)?;
        }
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
    use ark_relations::r1cs::ConstraintSystem;
    use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_std::UniformRand;

    #[test]
    fn feldman() {
        let mut rng = ark_std::test_rng();
        let n = 500;
        let secrets = (0..n)
            .map(|_| <E as PairingEngine>::Fr::rand(&mut rng))
            .collect::<Vec<_>>();
        let circuit = FeldmanCommit::<E, EV>::new(secrets.clone());
        //let cs = ConstraintSystem::<<E as PairingEngine>::Fq>::new_ref();
        //circuit.generate_constraints(cs.clone()).unwrap();
        //println!("Num constraints: {}", cs.num_constraints());
        //assert!(cs.is_satisfied().unwrap());
        //
        //
        let circuit2 = FeldmanCommit::<E, EV>::new(secrets.clone()); // why can't I clne :(
        let circuit3 = FeldmanCommit::<E, EV>::new(secrets); // why can't I clne :(
        let (pk, vk) = Groth16::<P>::setup(circuit2, &mut rng).unwrap();
        let proof = Groth16::prove(&pk, circuit3, &mut rng).unwrap();
        let valid_proof = Groth16::verify(&vk, &vec![], &proof).unwrap();
        assert!(valid_proof);
    }
}
