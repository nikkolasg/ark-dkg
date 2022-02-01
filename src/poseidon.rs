use crate::parameters::*;
use ark_bls12_377::Fq;
use ark_sponge::poseidon::PoseidonParameters;
use std::str::FromStr;

// can't use the following because 0.3.0 doesn't have this struct
/*impl PoseidonDefaultParameters for params {*/
//const PARAMS_OPT_FOR_CONSTRAINTS: [PoseidonDefaultParametersEntry; 7] = [
//PoseidonDefaultParametersEntry::new(2, 17, 8, 31, 0),
//PoseidonDefaultParametersEntry::new(3, 5, 8, 56, 0),
//PoseidonDefaultParametersEntry::new(4, 5, 8, 56, 0),
//PoseidonDefaultParametersEntry::new(5, 5, 8, 57, 0),
//PoseidonDefaultParametersEntry::new(6, 5, 8, 57, 0),
//PoseidonDefaultParametersEntry::new(7, 5, 8, 57, 0),
//PoseidonDefaultParametersEntry::new(8, 5, 8, 57, 0),
//];
//const PARAMS_OPT_FOR_WEIGHTS: [PoseidonDefaultParametersEntry; 7] = [
//PoseidonDefaultParametersEntry::new(2, 257, 8, 13, 0),
//PoseidonDefaultParametersEntry::new(3, 257, 8, 13, 0),
//PoseidonDefaultParametersEntry::new(4, 257, 8, 13, 0),
//PoseidonDefaultParametersEntry::new(5, 257, 8, 13, 0),
//PoseidonDefaultParametersEntry::new(6, 257, 8, 13, 0),
//PoseidonDefaultParametersEntry::new(7, 257, 8, 13, 0),
//PoseidonDefaultParametersEntry::new(8, 257, 8, 13, 0),
//];
//}

// returns optimized for constraints
pub fn get_bls12377_fq_params(_rate: usize) -> PoseidonParameters<Fq> {
    let arks = P1["ark"]
        .members()
        .map(|ark| {
            ark.members()
                .map(|v| Fq::from_str(v.as_str().unwrap()).unwrap())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mds = P1["mds"]
        .members()
        .map(|m| {
            m.members()
                .map(|v| Fq::from_str(v.as_str().unwrap()).unwrap())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    PoseidonParameters::new(
        P1["full_rounds"].as_u32().unwrap(),
        P1["partial_rounds"].as_u32().unwrap(),
        P1["alpha"].as_u64().unwrap(),
        mds,
        arks,
    )
}

#[cfg(test)]
mod test {
    use ark_bls12_377::{
        constraints::{G1Var, PairingVar as IV},
        Bls12_377 as I, Fq, Fr, G1Projective,
    };
    use ark_ec::ProjectiveCurve;

    use super::*;
    use ark_ff::{BigInteger, PrimeField};
    use ark_nonnative_field::AllocatedNonNativeFieldVar;

    use ark_r1cs_std::{fields::fp::FpVar, groups::CurveVar, prelude::*};
    use ark_relations::{
        ns,
        r1cs::{ConstraintLayer, ConstraintSystem, TracingMode},
    };
    use ark_sponge::{
        constraints::CryptographicSpongeVar,
        poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
        CryptographicSponge,
    };

    use ark_std::UniformRand;

    #[test]
    fn poseidon() {
        let params = get_bls12377_fq_params(2);
        let mut rng = ark_std::test_rng();

        let point = G1Projective::rand(&mut rng);
        let point_affine = point.into_affine();
        let scalar = Fr::rand(&mut rng);
        let scalar_in_fq = &Fq::from_repr(<Fq as PrimeField>::BigInt::from_bits_le(
            &scalar.into_repr().to_bits_le(),
        ))
        .unwrap(); // because Fr < Fq

        let mut sponge = PoseidonSponge::new(&params);
        sponge.absorb(&point_affine);
        sponge.absorb(&scalar_in_fq);
        let hash = sponge.squeeze_field_elements::<Fq>(1).remove(0);

        let cs = ConstraintSystem::<Fq>::new_ref();
        let mut sponge_var = PoseidonSpongeVar::new(cs.clone(), &params);
        let exp_hash_var =
            FpVar::<Fq>::new_witness(ns!(cs.clone(), "hashvar"), || Ok(hash.clone())).unwrap();
        let point_var_affine = G1Var::new_variable_omit_prime_order_check(
            ns!(cs.clone(), "point"),
            || Ok(point.clone()),
            AllocationMode::Witness,
        )
        .unwrap()
        // TODO rename that to into_affine
        .to_affine()
        .unwrap();
        sponge_var.absorb(&point_var_affine);

        let scalar_var =
            FpVar::new_witness(ns!(cs.clone(), "scalar var"), || Ok(scalar_in_fq)).unwrap();
        sponge_var.absorb(&scalar_var);
        let bits_scalar_var: Vec<Boolean<Fq>> = scalar_var.to_bits_le().unwrap();
        // checking if bits representation is the same
        /*let bits_scalar_native = scalar.into_repr().to_bits_le();*/
        //assert!(bits_scalar_var.len() >= bits_scalar_native.len());
        //for (native, var) in bits_scalar_native
        //.iter()
        //.take(256)
        //.zip(bits_scalar_var.iter())
        //{
        //assert_eq!(native, &var.value().unwrap(), "bits not equal");
        /*}*/
        //sponge_var.absorb(&bits_scalar);

        // now let's check with the non variable one
        let hash_var = sponge_var.squeeze_field_elements(1).unwrap().remove(0);
        hash_var.enforce_equal(&exp_hash_var).unwrap();

        // Test to see how many Fq ar eneeded to represent an Fr -
        // it's 15 ! crazy knowing that Fr < Fq ...!?
        /*let scalar_in_fq_var =*/
        let nonnative_scalar =
            AllocatedNonNativeFieldVar::<Fr, Fq>::new_witness(ns!(cs.clone(), "nonnative"), || {
                Ok(scalar)
            })
            .unwrap();
        let bits_scalar_nonnative = nonnative_scalar.to_bits_le().unwrap();
        for (var, nonnative) in bits_scalar_var
            .iter()
            .take(256)
            .zip(bits_scalar_nonnative.iter())
        {
            var.enforce_equal(nonnative).unwrap();
        }
        //println!(
        //"number of basefield elements: {} {:?} {}",
        //scalar_in_fq_var.limbs.len(),
        //scalar_in_fq_var.num_of_additions_over_normal_form,
        //scalar_in_fq_var.is_in_the_normal_form
        /*);*/

        println!("Num constraints: {}", cs.num_constraints());
        assert!(cs.is_satisfied().unwrap());
    }
}
