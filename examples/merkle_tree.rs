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
    // Define the circuit configuration.
    let config = CircuitConfig::standard_recursion_config();
    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    // Create the circuit builder.
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // The input variables.
    let leaf = builder.add_virtual_target();
    let root = builder.add_virtual_target();
    let path_elements = builder.add_input_array(D, F::default());
    let path_indices = builder.add_input_array(D, F::default());

    // Create the selectors and hashers.
    let mut selectors = Vec::new();
    let mut hashers = Vec::new();
    for i in 0..D {
        selectors.push(builder.add_component(DualMux::<F>));
        hashers.push(builder.add_component(HashLeftRight::<F>));
    }

    // Connect the components.
    for i in 0..D {
        selectors[i].in[0] <== if i == 0 { leaf } else { hashers[i - 1].hash };
        selectors[i].in[1] <== path_elements[i];
        selectors[i].s <== path_indices[i];

        hashers[i].left <== selectors[i].out[0];
        hashers[i].right <== selectors[i].out[1];
    }

    // Connect the root.
    root === hashers[D - 1].hash;

    // Generate the circuit data.
    let data = builder.build::<C>();
    let mut pw = PartialWitness::<F>::new();

    // Provide initial values.
    pw.set_target(leaf, F::from_canonical_u32(17));
    pw.set_target_arr(path_elements, [F::from_canonical_u32(1), F::from_canonical_u32(2)]);
    pw.set_input_arr(path_indices, [F::from_canonical_u32(0), F::from_canonical_u32(1)]);

    // Generate the proof.
    let proof = data.prove(pw)?;
    data.verify(proof)?;

    Ok(())
}