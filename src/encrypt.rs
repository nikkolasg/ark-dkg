use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::{fields::Field, BitIteratorLE, PrimeField};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::groups::bls12;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::poseidon::{constraints::PoseidonSpongeVar, PoseidonParameters, PoseidonSponge};
use ark_sponge::{constraints::AbsorbGadget, Absorb, CryptographicSponge};
use ark_std::marker::PhantomData;
use ark_std::rand::Rng;
use ark_std::vec::Vec;
use ark_std::UniformRand;
use std::ops::MulAssign;

use ark_bls12_377::{constraints::*, *};
//
// ElGamal encryption E = { g^r, H((g^x)^r) + secret }
// Circuit will do the following
//  - take the random "r" and multiply by the public key
//  - hash the result and add with the secret
//  - verify the result is equal the second part of encryption given as public input
//  - take the random "r" and multiply by the generator
//  - verify the result is equal the first part of the encryption given as
//  public input
pub struct EncryptCircuit<C, CV>
where
    C: ProjectiveCurve,
    C::BaseField: PrimeField, // Prime for constraint CV
    CV: CurveVar<C, C::BaseField> + AllocVar<C, C::BaseField>,
{
    r: Vec<C::ScalarField>,
    pub_keys: Vec<C>,
    enc: Vec<C::ScalarField>, // H(g^y^r) + msg
    grs: Vec<C>,
    pub_rs: Vec<C>,
    msgs: Vec<C::ScalarField>,
    params: PoseidonParameters<C::BaseField>,
    _curvevar: PhantomData<CV>,
}

impl<C, CV> EncryptCircuit<C, CV>
where
    C: ProjectiveCurve,
    C::BaseField: PrimeField,
    C::Affine: Absorb, // because I absorb affine coordinates
    CV: CurveVar<C, C::BaseField> + AllocVar<C, C::BaseField> + AbsorbGadget<C::BaseField>,
{
    pub fn new<R: Rng>(
        msgs: Vec<C::ScalarField>,
        pub_keys: Vec<C>,
        params: PoseidonParameters<C::BaseField>,
        rng: &mut R,
    ) -> Self {
        let rs = (0..pub_keys.len())
            .map(|_| C::ScalarField::rand(rng))
            .collect::<Vec<_>>();
        let grs = rs
            .iter()
            .map(|r| {
                let mut g = C::prime_subgroup_generator();
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
            .collect::<Vec<C>>();
        // we want the output
        let enc = pubrs
            .iter()
            .zip(msgs.iter())
            .map(|(pr, msg)| {
                let mut sponge = PoseidonSponge::new(&params);
                let pra = pr.into_affine();
                //sponge.absorb(&pra.xy().0);
                sponge.absorb(&pra);
                let dh = sponge.squeeze_field_elements::<C::ScalarField>(1)[0];
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
            _curvevar: PhantomData,
        }
    }

    pub fn verify_encryption(
        &self,
        cs: ConstraintSystemRef<C::BaseField>,
        native_msgs: &[NonNativeFieldVar<C::ScalarField, C::BaseField>],
    ) -> Result<(), SynthesisError> {
        let g = CV::new_variable_omit_prime_order_check(
            ark_relations::ns!(cs, "generator"),
            || Ok(C::prime_subgroup_generator()),
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
            .iter()
            .map(|gr| {
                CV::new_variable_omit_prime_order_check(
                    ark_relations::ns!(cs, "gr"),
                    || Ok(gr.clone()),
                    AllocationMode::Input,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (rvar, grvar) in rvars.iter().zip(grvars.iter()) {
            let exp = g.scalar_mul_le(rvar.iter())?;
            grvar.enforce_equal(&exp)?;
        }

        // now do the encryption
        let poseidon = PoseidonSpongeVar::new(cs.clone(), &self.params);
        let pubrs = self
            .pub_rs
            .iter()
            .map(|p|
                // need affine form to get the x coordinate
                CV::new_variable_omit_prime_order_check(
                    ark_relations::ns!(cs,"pubrs"),
                    || Ok(p.clone()),
                    AllocationMode::Input,
                )) //.and_then(|g1var| g1var.affine_coords()))
            .collect::<Result<Vec<_>, _>>()?;

        // put the msgs (evaluation of poly) as non native field element
        // now do the encryption !
        let computeds = pubrs
            .into_iter()
            .zip(native_msgs.into_iter())
            .map(|(coords, msg)| {
                let mut poseidon = PoseidonSpongeVar::new(cs.clone(), &self.params);
                // TODO: this absorbs both X and Y and Infinity symbol making 3
                // vars per hash, which is way too much - we only need x
                // Making this is hard because of the type system.
                poseidon.absorb(&coords);
                poseidon
                    .squeeze_nonnative_field_elements::<C::ScalarField>(1)
                    .and_then(|r| Ok(r.0[0].clone() + msg))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let expecteds = self
            .enc
            .iter()
            .map(|exp| {
                NonNativeFieldVar::<C::ScalarField, C::BaseField>::new_witness(
                    ark_relations::ns!(cs, "enc"),
                    || Ok(exp),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (comp, exp) in computeds.iter().zip(expecteds.iter()) {
            comp.enforce_equal(exp)?;
        }
        Ok(())
    }
}

impl<C, CV> ConstraintSynthesizer<C::BaseField> for EncryptCircuit<C, CV>
where
    C: ProjectiveCurve,
    C::BaseField: PrimeField + Absorb,
    C::Affine: Absorb,
    CV: CurveVar<C, C::BaseField> + AllocVar<C, C::BaseField> + AbsorbGadget<C::BaseField>,
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<C::BaseField>,
    ) -> Result<(), SynthesisError> {
        let native_msgs = self
            .msgs
            .iter()
            .map(|m| {
                NonNativeFieldVar::<C::ScalarField, C::BaseField>::new_witness(
                    ark_relations::ns!(cs, "msgs"),
                    || Ok(m.clone()),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        self.verify_encryption(cs, &native_msgs)
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
        let circuit =
            EncryptCircuit::<G1Projective, G1Var>::new(secrets, pubkeys, params, &mut rng);
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
