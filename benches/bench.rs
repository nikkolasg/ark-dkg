use ark_bls12_377::{constraints::PairingVar as IV, Bls12_377 as I, Fr};
use ark_bw6_761::BW6_761 as O;
use ark_ec::PairingEngine;
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
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
    verifying: u128,
    verifying_total: u128,
}

fn main() {
    let mut rng = ark_std::test_rng();
    let mut writer = csv::Writer::from_path("dkg_snark.csv").expect("unable to open csv writer");
    let n_sizes = vec![5, 50, 100, 500, 800];
    //let n_sizes = [5];
    let params = poseidon::get_bls12377_fq_params(2);

    let _values = n_sizes
        .into_iter()
        .map(|n| {
            let mut br = BenchResult::default();
            println!("Starting bench for n = {}", n);
            let degree = n / 2;
            let threshold = degree + 1;
            br.n = n as usize;
            br.thr = threshold;
            println!("\tAllocating ids & coeffs...");
            // create pk, vk for inner proof
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
            let secret = Fr::rand(&mut rng);
            let coeffs = std::iter::once(secret.clone())
                .chain((0..threshold - 2).map(|_| Fr::rand(&mut rng)))
                .collect::<Vec<Fr>>();

            println!("\tAllocating PolyCircuit pk & vk...");
            let (pk, vk) = {
                let pe = PolyCircuit::<Fr>::new(coeffs.clone(), ids);
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
                poseidon_params: params.clone(),
            };
            br.total_constraints = {
                println!("\tAllocating DKGCircuit for constraints...");
                let circuit = DKGCircuit::<I, IV>::new(config.clone(), &mut rng).unwrap();
                let cs = ConstraintSystem::<<I as PairingEngine>::Fq>::new_ref();
                circuit.generate_constraints(cs.clone()).unwrap();
                cs.num_constraints()
            };

            let (opk, opvk) = {
                println!("\tAllocating DKGCircuit for Groth16 setup ...");
                let circuit = DKGCircuit::<I, IV>::new(config.clone(), &mut rng).unwrap();
                println!("\tDKGCircuit Groth16 setup ...");
                let (opk, ovk) = Groth16::setup(circuit, &mut rng).unwrap();
                let opvk = Groth16::<O>::process_vk(&ovk).unwrap();
                (opk, opvk)
            };

            println!("\tAllocating DKGCircuit final instance...");
            let start = Instant::now();
            let circuit = DKGCircuit::<I, IV>::new(config, &mut rng).unwrap();
            br.proving += start.elapsed().as_millis();

            let start = Instant::now();
            let input = vec![circuit.input_commitment()];
            br.verifying_total = start.elapsed().as_millis();

            // TODO make a macro
            let start = Instant::now();
            println!("\tProving...");
            let oproof = Groth16::<O>::prove(&opk, circuit, &mut rng).unwrap();
            br.proving += start.elapsed().as_millis();

            let start = Instant::now();
            println!("\tVerifying...");
            ark_groth16::verify_proof(&opvk, &oproof, &input).unwrap();
            // verifying takes into account the time to compute the hashed
            // commitment
            let verifying = start.elapsed().as_millis();
            br.verifying += verifying;
            br.verifying_total += verifying;
            writer
                .serialize(br)
                .expect("unable to write results to csv");
            writer.flush().expect("wasn't able to flush");
        })
        .collect::<Vec<_>>();
}
