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
