use ark_bls12_377::{constraints::PairingVar as IV, Bls12_377 as I, Fr};
use ark_bw6_761::BW6_761 as O;
use ark_ec::PairingEngine;
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintLayer, ConstraintSynthesizer, ConstraintSystem, TracingMode};
use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_std::UniformRand;
use dkg_snark::*;
use serde::Serialize;
use std::time::Instant;

#[derive(Default, Clone, Debug, Serialize)]
struct BenchResult {
    n: usize,
    thr: usize,
    inner_constraints: usize,
    total_constraints: usize,
    proving: u128,
    verifying: u128, // useless since no public input so far
}

fn main() {
    let mut rng = ark_std::test_rng();
    let mut writer = csv::Writer::from_path("dkg_snark.csv").expect("unable to open csv writer");
    //let n_sizes = vec![50, 100, 300, 500, 700, 900, 1100];
    let n_sizes = [5];
    let _values = n_sizes
        .into_iter()
        .map(|n| {
            let mut br = BenchResult::default();
            println!("Starting bench for n = {}", n);
            let degree = n / 2;
            let threshold = degree + 1;
            br.n = n as usize;
            br.thr = threshold;
            let secret = Fr::rand(&mut rng);
            let ids = (0..n).map(|i| Fr::from((i + 1) as u32)).collect::<Vec<_>>();
            let participants = (0..n)
                .map(
                    |_| <I as PairingEngine>::G1Projective::rand(&mut rng), // dont care for the moment
                )
                .zip(ids.iter())
                .map(|(p, idx)| Node {
                    idx: idx.clone(),
                    key: p,
                })
                .collect::<Vec<_>>();
            // create pk, vk for inner proof
            let (pk, vk) = {
                let coeffs = std::iter::once(secret.clone())
                    .chain((0..threshold - 2).map(|_| Fr::rand(&mut rng)))
                    .collect::<Vec<_>>();
                let pe = PolyCircuit::<Fr>::new(coeffs, ids.clone());
                // XXX is there a way to get this info without running twice the
                // QAP transformation ?
                let cs = ConstraintSystem::<<I as PairingEngine>::Fr>::new_ref();
                pe.clone().generate_constraints(cs.clone()).unwrap();
                br.inner_constraints = cs.num_constraints();

                Groth16::setup(pe, &mut rng).unwrap()
            };
            let pvk = Groth16::<I>::process_vk(&vk).unwrap();

            //
            let config = DKGConfig {
                secret: secret,
                threshold: threshold,
                participants: participants,
                inner_pk: pk,
                inner_vk: pvk,
                poseidon_params: poseidon::get_bls12377_fq_params(2),
            };
            let circuit = DKGCircuit::<I, IV>::new(config.clone(), &mut rng).unwrap();
            let cs = ConstraintSystem::<<I as PairingEngine>::Fq>::new_ref();
            circuit.generate_constraints(cs.clone()).unwrap();
            br.total_constraints = cs.num_constraints();

            let circuit = DKGCircuit::<I, IV>::new(config.clone(), &mut rng).unwrap();
            let (opk, ovk) = Groth16::setup(circuit, &mut rng).unwrap();
            let opvk = Groth16::<O>::process_vk(&ovk).unwrap();
            let circuit = DKGCircuit::<I, IV>::new(config, &mut rng).unwrap();

            // TODO make a macro
            let start = Instant::now();
            let oproof = Groth16::<O>::prove(&opk, circuit, &mut rng).unwrap();
            br.proving = start.elapsed().as_millis();

            let start = Instant::now();
            ark_groth16::verify_proof(&opvk, &oproof, &vec![]).unwrap();
            br.verifying = start.elapsed().as_millis();
            writer
                .serialize(br)
                .expect("unable to write results to csv");
        })
        .collect::<Vec<_>>();
    writer.flush().expect("wasn't able to flush");
}