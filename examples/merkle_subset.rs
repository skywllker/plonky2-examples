use anyhow::Result;
use plonky2::hash::poseidon::PoseidonHash;
use rand::rngs::OsRng;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;

use std::time::Instant;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData, VerifierOnlyCircuitData, VerifierCircuitData};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig, Hasher};
use plonky2::plonk::proof::ProofWithPublicInputs;
use plonky2::hash::hash_types::RichField;

use plonky2::field::extension::Extendable;

// Recursively validated proof of 5**x 
#[derive(Clone)]
pub struct ProofTuple<F: RichField+Extendable<D>, C:GenericConfig<D, F=F>, const D: usize>{
    proof: ProofWithPublicInputs<F, C, D>,
    vd: VerifierOnlyCircuitData<C, D>,
    cd: CommonCircuitData<F, D>,
    depth: u32,
}



// generates ground proof for a step
pub fn ground_proof<F: RichField + Extendable<D>, C: GenericConfig<D, F=F>, const D: usize, const B: usize>(inp1: &[F; 4], inp2: &[F; 4], cutoff: usize)->ProofTuple<F,C,D>{
    let real_zero = F::ZERO;
    let zero_hash = PoseidonHash::hash_no_pad(&real_zero.collect::<Vec<F>>());

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // aritmatic circuit to input1 = input2 or input2 = 0     
    let input1 = builder.add_virtual_target();
    let input2 = builder.add_virtual_target();
    let temp1 = builder.sub(input1, input2);
    let temp2 = builder.neg(input2);
    let temp3 = builder.add_const(temp2, real_zero);
    let temp4 = builder.mul(temp1, temp3);
    builder.assert_zero(temp4);


    let mut pw = PartialWitness::new();

    builder.register_public_input(input1);
    builder.register_public_input(input2);

    let data = builder.build::<C>();
    let proof = data.prove(pw).unwrap();

    ProofTuple{
        proof, 
        vd: data.verifier_only, 
        cd: data.common,
        depth: 0
    }
}


/// This function merges two proofs with 2 public inputs each, treated as follows: 0 is "input", 1 is "output"
/// It requires that output of the first proof is the input of the second
/// It exposes the input of the first proof and the output of the second
pub fn recursive_proof<
F: RichField + Extendable<D>,
C: GenericConfig<D, F = F>,
const D: usize,
>(
inner_l: &ProofTuple<F, C, D>, inner_r: &ProofTuple<F,C,D>,
) -> Result<ProofTuple<F, C, D>>
where
C::Hasher: AlgebraicHasher<F>,   
{
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
//    assert_eq!(inner_l.depth, inner_r.depth, "Trying to merge proofs of different depth!");

    let pt_l = builder.add_virtual_proof_with_pis(& inner_l.cd);
    let pt_r = builder.add_virtual_proof_with_pis(& inner_r.cd);

    let inner_vdt_l = builder.add_virtual_verifier_data(inner_l.cd.config.fri_config.cap_height);
    let inner_vdt_r = builder.add_virtual_verifier_data(inner_r.cd.config.fri_config.cap_height);
    
    builder.verify_proof::<C>(&pt_l, &inner_vdt_l, &inner_l.cd);
    builder.verify_proof::<C>(&pt_r, &inner_vdt_r, &inner_r.cd);

    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target::<C, D>(& pt_l, & inner_l.proof);
    pw.set_proof_with_pis_target::<C, D>(& pt_r, & inner_r.proof);
    pw.set_verifier_data_target::<C,D>(& inner_vdt_l, & inner_l.vd);
    pw.set_verifier_data_target::<C,D>(& inner_vdt_r, & inner_r.vd);

    // hash (pt_l.public_inputs[0], pt_r.public_inputs[0]) register this as public input
    // hash (pt_l.public_inputs[1], pt_r.public_inputs[1]) register this as public input

    let data = builder.build::<C>();
    
    let proof = data.prove(pw).unwrap();
    Ok(ProofTuple{proof, vd: data.verifier_only, cd: data.common, depth: inner_l.depth+1})

}

// this function generates the tree of proofs recursively
pub fn recursive_tree<F: RichField + Extendable<D>, C:GenericConfig<D, F=F>, const D: usize>
    (
        location: u64,
        mut ground_size: usize,
        height: usize,
        trivial_proofs: &Vec<ProofTuple<F,C,D>>,
    )->ProofTuple<F,C,D> where <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>
    {
        if height > 1 {
            ground_size = trivial_proofs.len() as usize;
            ground_size = ground_size / 2;
            let sec = ground_size as u64;
            let first_tuple = recursive_tree::<F, C, D>(location, ground_size, height-1, &trivial_proofs[0..ground_size].to_vec());
            let second_tuple = recursive_tree::<F, C, D>(location+sec, ground_size,  height-1, &trivial_proofs[ground_size..ground_size*2].to_vec());
            let merged_tuple = recursive_proof(&first_tuple, &second_tuple).unwrap();
            return merged_tuple;
        }
        else {
            let merged_tuple = recursive_proof(&trivial_proofs[0], &trivial_proofs[1]).unwrap();
            return merged_tuple;
        }
    }

// This function runs the whole thing.
pub fn run<
        F: RichField + Extendable<D>,
        C:GenericConfig<D, F=F>,
        const D: usize> (init_value: u64)
            ->
        Result<VerifierCircuitData<F,C,D>>
            where
        C::Hasher: AlgebraicHasher<F>, 
    {

    // This is the amount of stacked hashes we put into the elementary ground proof. In theory, optimal behaviour is having it big enough such that the
    // execution time of the ground proof is ~ equivalent to the recursive proof exec time.

    const BATCH_SIZE: usize = 4;

    // this is the total depth of recursion batches. pow(2, depth)*BATCH_SIZE hashes must be infeasible to do sequentially.
    const DEPTH: usize = 2;

    let tmp = Instant::now();
    // Trivial proof phase computation, it can be separated into the precompute phase with the small modification of the circuit; and recursive circuit
    // I'm a bit too lazy to mess with this now. This phase will take < time than the main phase in any case.
    let mut trivial_proofs = Vec::new();
    trivial_proofs.push(ground_proof::<F,C,D,BATCH_SIZE>(init_value));
    let mut x = init_value;
    for i in 1..BATCH_SIZE {
        println!("={:#?}", trivial_proofs[i-1].proof.public_inputs);
        x = x*5;
        trivial_proofs.push(ground_proof::<F,C,D,BATCH_SIZE>(x));

    }
    println!("FOR LOOOOP FİNİSHED");

    println!("Lets come to final proof!");
    let final_proof = recursive_tree::<F,C,D>(0, BATCH_SIZE, DEPTH, &trivial_proofs);
    println!("Final proofs public inputs: {:#?}", final_proof.proof.public_inputs);
    // final proof public inputs should be root of original merkle tree
    // and root of subset merkle tree if the subset is really a subset of original
    
    let tmp2 = Instant::now();
    println!("Computation took {}ms", (tmp2-tmp).as_millis());

    println!("Allegedly, the result of our poseidon is: {:#?}",
        final_proof.proof.public_inputs,
     );
    println!("Proof size: {} bytes\n",final_proof.proof.to_bytes().len());
    Ok(VerifierCircuitData::<F,C,D>{verifier_only: final_proof.vd, common: final_proof.cd})
}

pub fn test() -> Result<()> {
    
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    
    let rng_seed = OsRng::default().next_u64();
    let mut rng = ChaCha8Rng::seed_from_u64(rng_seed);

    let input = F::ONE;
    let init_value = 5;


    let mut cutoff = (rng.next_u64() % 35) as u128;

    
    let vd1 = run::<F,C,D>(init_value)?; // Currently not using rayon. Maybe should (it gives some performance gain even on my machine).

    println!("Run again to check that the verifier data of the final proof is the same!\n");

    cutoff = (rng.next_u64() % 10000) as u128;



    let vd2 = run::<F,C,D>(init_value)?;

    println!("Checking that verifier circuit data is the same for two proofs! \n");

    assert_eq!(vd1.verifier_only, vd2.verifier_only);
    assert_eq!(vd1.common, vd2.common);
    println!("Victory! :3");
    Ok(())
}


fn main() -> Result<()> {
    test()
}