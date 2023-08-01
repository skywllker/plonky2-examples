use pow_of5_circuit::{F, Circuit};
use plonky2::field::types::Field;

mod pow_of5_circuit;

fn main() {

    // create circuit struct
    let circuit = Circuit {
        input: F::from_canonical_u64(25),
        output: F::from_canonical_u64(125)
    };

    // make circuit 
    let (input, output, circuit_instance) = circuit.make_circuit().unwrap();

    // prove and verify data
    circuit.create_and_verify_proof( input, output, circuit_instance).unwrap()
}