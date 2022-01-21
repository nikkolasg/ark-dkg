use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{fields::Field, BitIteratorLE, PrimeField};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::groups::bls12;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::poseidon::{constraints::PoseidonSpongeVar, PoseidonParameters, PoseidonSponge};
use ark_sponge::CryptographicSponge;
use ark_std::marker::PhantomData;
use ark_std::rand::Rng;
use ark_std::vec::Vec;
use ark_std::UniformRand;
use std::ops::MulAssign;

use ark_bls12_377::{constraints::*, *};
type ConstraintF = <<G1Affine as AffineCurve>::BaseField as Field>::BasePrimeField;
//
// ElGamal encryption E = { g^r, H((g^x)^r) + secret }
// Circuit will do the following
//  - take the random "r" and multiply by the public key
//  - hash the result and add with the secret
//  - verify the result is equal the second part of encryption given as public input
//  - take the random "r" and multiply by the generator
//  - verify the result is equal the first part of the encryption given as
//  public input
pub struct EncryptCircuit {
    r: Vec<Fr>,
    pub_keys: Vec<G1Projective>,
    enc: Vec<Fr>, // H(g^y^r) + msg
    grs: Vec<G1Projective>,
    pub_rs: Vec<G1Projective>,
    msgs: Vec<Fr>,
    params: PoseidonParameters<Fq>,
}

impl EncryptCircuit {
    pub fn new<R: Rng>(
        msgs: Vec<Fr>,
        pub_keys: Vec<G1Projective>,
        params: PoseidonParameters<ConstraintF>,
        rng: &mut R,
    ) -> Self {
        let rs = (0..pub_keys.len())
            .map(|_| Fr::rand(rng))
            .collect::<Vec<_>>();
        let grs = rs
            .iter()
            .map(|r| {
                let mut g = G1Projective::prime_subgroup_generator();
                g.mul_assign(r.clone());
                g
            })
            .collect::<Vec<_>>();
        let pubrs = rs
            .iter()
            .zip(pub_keys.iter())
            .map(|(r, p)| {
                let mut pp = p.clone();
                pp.mul_assign(r.clone());
                pp
            })
            .collect::<Vec<_>>();
        // we want the output
        let enc = pubrs
            .iter()
            .zip(msgs.iter())
            .map(|(pr, msg)| {
                let mut sponge = PoseidonSponge::<ConstraintF>::new(&params);
                let pra = pr.into_affine();
                sponge.absorb(&pra.x);
                let dh = sponge.squeeze_field_elements::<Fr>(1)[0];
                dh + msg
            })
            .collect::<Vec<_>>();
        Self {
            r: rs,
            msgs: msgs,
            pub_keys: pub_keys,
            enc: enc,
            grs: grs,
            pub_rs: pubrs,
            params: params,
        }
    }
}

impl ConstraintSynthesizer<Fq> for EncryptCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let g = G1Var::new_variable_omit_on_curve_check(
            ark_relations::ns!(cs, "generator"),
            || Ok(G1Projective::prime_subgroup_generator()),
            AllocationMode::Input,
        )?;
        // verify consistency with grs
        let rvars = self
            .r
            .iter()
            .map(|r| {
                let bits: Vec<bool> = BitIteratorLE::new(r.into_repr().as_ref().to_vec()).collect();
                let rbits = Vec::new_witness(ark_relations::ns!(cs, "rbits"), || Ok(bits))?;
                Ok(rbits)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let grvars = self
            .grs
            .into_iter()
            .map(|gr| {
                G1Var::new_variable_omit_on_curve_check(
                    ark_relations::ns!(cs, "gr"),
                    || Ok(gr),
                    AllocationMode::Input,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (rvar, grvar) in rvars.iter().zip(grvars.iter()) {
            let exp = g.scalar_mul_le(rvar.iter())?;
            grvar.enforce_equal(&exp)?;
        }

        // now do the encryption
        let poseidon = PoseidonSpongeVar::<Fq>::new(cs.clone(), &self.params);
        let pubrs = self
            .pub_rs
            .into_iter()
            .map(|p|
                // need affine form to get the x coordinate
                G1Var::new_variable_omit_prime_order_check(
                    ark_relations::ns!(cs,"pubrs"),
                    || Ok(p),
                    AllocationMode::Input,
                ).and_then(|g1var| g1var.to_affine()))
            .collect::<Result<Vec<_>, _>>()?;

        // put the msgs (evaluation of poly) as non native field element
        let native_msgs = self
            .msgs
            .into_iter()
            .map(|m| {
                NonNativeFieldVar::<Fr, Fq>::new_witness(ark_relations::ns!(cs, "msgs"), || Ok(m))
            })
            .collect::<Result<Vec<_>, _>>()?;
        // now do the encryption !
        let computeds = pubrs
            .into_iter()
            .zip(native_msgs.into_iter())
            .map(|(pr, msg)| {
                let mut poseidon = PoseidonSpongeVar::<Fq>::new(cs.clone(), &self.params);
                poseidon.absorb(&pr.x);
                poseidon
                    .squeeze_nonnative_field_elements::<Fr>(1)
                    .and_then(|r| Ok(r.0[0].clone() + msg))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let expecteds = self
            .enc
            .iter()
            .map(|exp| {
                NonNativeFieldVar::<Fr, Fq>::new_witness(ark_relations::ns!(cs, "enc"), || Ok(exp))
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (comp, exp) in computeds.iter().zip(expecteds.iter()) {
            comp.enforce_equal(exp)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    //use ark_bw6_761::BW6_761 as P;
    //use ark_ec::AffineCurve;
    //use ark_groth16::Groth16;
    use ark_relations::r1cs::ConstraintSystem;
    //use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_std::UniformRand;

    #[test]
    fn encrypt() {
        let mut rng = ark_std::test_rng();
        let n = 5;
        let secrets = (0..n).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();
        let pubkeys = (0..n)
            .map(|_| G1Projective::rand(&mut rng))
            .collect::<Vec<_>>();
        let params = crate::poseidon::get_bls12377_fq_params(2);
        let circuit = EncryptCircuit::new(secrets, pubkeys, params, &mut rng);
        let cs = ConstraintSystem::<Fq>::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();
        println!("Num constraints: {}", cs.num_constraints());
        assert!(cs.is_satisfied().unwrap());
        /*let circuit2 = PolyCircuit::<E, EV>::new(secrets.clone()); // why can't I clne :(*/
        //let circuit3 = PolyCircuit::<E, EV>::new(secrets); // why can't I clne :(
        //let (pk, vk) = Groth16::<P>::setup(circuit2, &mut rng).unwrap();
        //let proof = Groth16::prove(&pk, circuit3, &mut rng).unwrap();
        //let valid_proof = Groth16::verify(&vk, &vec![], &proof).unwrap();
        /*assert!(valid_proof);*/
    }
}
