use ark_ec::ProjectiveCurve;
use ark_ff::{fields::Field, BitIteratorLE, PrimeField};
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_sponge::poseidon::{PoseidonParameters, PoseidonSponge};
use ark_sponge::CryptographicSponge;
use ark_std::marker::PhantomData;
use ark_std::rand::Rng;
use ark_std::vec::Vec;
use ark_std::UniformRand;

type ConstraintF<C> = <<C as ProjectiveCurve>::BaseField as Field>::BasePrimeField;
// ElGamal encryption E = { g^r, H((g^x)^r) + secret }
// Circuit will do the following
//  - take the random "r" and multiply by the public key
//  - hash the result and add with the secret
//  - verify the result is equal the second part of encryption given as public input
//  - take the random "r" and multiply by the generator
//  - verify the result is equal the first part of the encryption given as
//  public input
pub struct EncryptCircuit<C: ProjectiveCurve, V: CurveVar<C, C::BaseField>> {
    r: Vec<C::ScalarField>,
    pub_keys: Vec<C>,
    enc: Vec<C::ScalarField>,
    grs: Vec<C>,
    _curve_gadget: PhantomData<V>,
}

impl<C, V> EncryptCircuit<C, V>
where
    C: ProjectiveCurve,
    V: CurveVar<C, C::BaseField>,
{
    pub fn new<R: Rng>(
        msgs: Vec<C::ScalarField>,
        pub_keys: Vec<C>,
        params: &PoseidonParameters<ConstraintF<C>>,
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
            .collect::<Vec<_>>();
        // we want the output
        let enc = pubrs
            .iter()
            .zip(msgs.iter())
            .map(|(pr, msg)| {
                let mut sponge = PoseidonSponge::<ConstraintF<C>>::new(params);
                let pra = pr.into_affine();
                sponge.absorb(pra.x);
                let dh = sponge.squeeze_field_elements::<C::ScalarField>(1)[0];
                let dh = C::ScalarField::rand(rng);
                dh + msg
            })
            .collect::<Vec<_>>();
        Self {
            r: rs,
            pub_keys: pub_keys,
            enc: enc,
            grs: grs,
            _curve_gadget: PhantomData,
        }
    }
}

impl<C, V> ConstraintSynthesizer<C::BaseField> for EncryptCircuit<C, V>
where
    C: ProjectiveCurve,
    V: CurveVar<C, C::BaseField>,
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<C::BaseField>,
    ) -> Result<(), SynthesisError> {
        let g = V::new_variable_omit_prime_order_check(
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
            .into_iter()
            .map(|gr| {
                V::new_variable_omit_prime_order_check(
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
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_377::{constraints::*, *};
    //use ark_bw6_761::BW6_761 as P;
    //use ark_ec::ProjectiveCurve;
    //use ark_groth16::Groth16;
    use ark_relations::r1cs::ConstraintSystem;
    //use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
    use ark_std::UniformRand;

    #[test]
    fn encrypt() {
        let mut rng = ark_std::test_rng();
        let n = 5;
        let secrets = (0..n)
            .map(|_| <G1Projective as ProjectiveCurve>::ScalarField::rand(&mut rng))
            .collect::<Vec<_>>();
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
