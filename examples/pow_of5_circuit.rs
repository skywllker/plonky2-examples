use plonky2::{
    field::{goldilocks_field::GoldilocksField, types::Field},
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::PoseidonGoldilocksConfig,
    },
};


pub type F = GoldilocksField;
pub type C = PoseidonGoldilocksConfig;

use anyhow::{Ok, Result};

pub struct Circuit {
    pub input: F,
    pub output: F,
}


impl Circuit {
    pub fn make_circuit(&self) -> Result<(Target, Target, CircuitData<F, C, 2>)> {
        // use standard config 
        let config = CircuitConfig::standard_recursion_config();
        // create builder from config
        let mut builder = CircuitBuilder::new(config);

        // aritmatic circuit to output = input * 5        
        let input = builder.add_virtual_target();
        let output = builder.mul_const(F::from_canonical_u64(5), input);
        
        // we set output is public
        builder.register_public_input(output);

        // build circuit
        let circuit = builder.build();

        // output circuit and target
        Ok((input, output, circuit))
    }

    pub fn create_and_verify_proof(
        &self,
        input: Target,
        output: Target,
        circuit: CircuitData<F, C, 2>,
    ) -> Result<()> {
        // partial witness is witness with input only
        let mut pw = PartialWitness::new();
        // we set input value for target
        pw.set_target(output, self.output);
        pw.set_target(input, self.input);
        
        // plonky2 auto compute full witness base on circuit
        let proof = circuit.prove(pw).unwrap();

        // verify proof 
        circuit.verify(proof)
    }
}

