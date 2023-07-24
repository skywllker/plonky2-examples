#![allow(clippy::upper_case_acronyms)]

use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

fn main() -> Result<()> {
    // take an x for x.factorial
    let x = 92;
    // general definitions for every circuit 
    // don't change if you don't change the field or etc.
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // The arithmetic circuit.
    let initial_a = builder.add_virtual_target();
    let mut cur_target = initial_a;

    for i in 1..x {
        let i_target = builder.constant(F::from_canonical_u32(i));
        cur_target = builder.mul(cur_target, i_target);
    }

    // Public inputs are the two initial values (provided below) and the result (which is generated).
    builder.register_public_input(initial_a);
    builder.register_public_input(cur_target);

    // Provide initial values.
    let mut pw = PartialWitness::new();
    pw.set_target(initial_a, F::ONE);

    let data = builder.build::<C>();
    let proof = data.prove(pw)?;

    println!(
        "x! mod |F| (starting with {}) is: {}",
        proof.public_inputs[0], proof.public_inputs[1]
    );

    data.verify(proof)


}