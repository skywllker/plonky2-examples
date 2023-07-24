use plonky2::{
    field::{goldilocks_field::GoldilocksField, types::Field},
    iop::witness::{PartialWitness, WitnessWrite},
    plonk::{
        circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
        config::PoseidonGoldilocksConfig,
    },
};

use anyhow::Result;

fn main() -> Result<()> {
    // We have a public input c
    // Proof that "I know a and b such that a * b = c"
    // My private inputs as a prover, a and b are 17 and 19, respectively.
    // The public input is c = 323.

    // standard proof setup
    let config = CircuitConfig::standard_recursion_config();
    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // The arithmetic circuit.
    let x_a = builder.add_virtual_target();
    let x_b = builder.add_virtual_target();
    let cur_target = builder.mul(x_a, x_b);

    // public input c
    let x_c = builder.add_virtual_target();
    builder.register_public_input(x_c);
    
    // constraint a * b = c
    builder.connect(cur_target, x_c);

    // generate circuit data
    let data = builder.build::<C>();
    let mut pw = PartialWitness::<F>::new();

    // Provide initial values.
    pw.set_target(x_a, F::from_canonical_u32(17));
    pw.set_target(x_b, F::from_canonical_u32(19));
    pw.set_target(x_c, F::from_canonical_u32(323));

    // Generate proof
    let proof = data.prove(pw)?;
    data.verify(proof)?;

    Ok(())
}