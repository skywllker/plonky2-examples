use plonky2::{
    field::{goldilocks_field::GoldilocksField, types::Field, extension::Extendable},
    iop::witness::{PartialWitness, WitnessWrite},
    iop::witness::Witness,
    iop::target::{BoolTarget, Target},
    hash::hash_types::RichField,
    plonk::{
        circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
        config::PoseidonGoldilocksConfig,
    },

};
use anyhow::Result;

fn change_type(v: usize) -> u32 {
    v as u32
}

fn NotEqual<F: RichField + Extendable<D>, const D: usize>(b: &mut CircuitBuilder<F, D>, x: Target, y: Target) {
    let k2 = b.one();
    let k1 = b.sub(x, y);
    let z = b.div(k2, y);; 
    let k = b.mul(z, k1);
    b.assert_zero(k);
}

fn AllDifferent<F: RichField + Extendable<D>, const D: usize>(b: &mut CircuitBuilder<F, D>, x: Vec<Target>) {
    for i in 0..x.len() {
        for j in i+1..x.len() {
           // let mut z = b.sub(x[i], x[j]);
           // b.assert_zero(z);
            NotEqual(b, x[i], x[j]);
        }
    }
}

fn main() -> Result<()> {
    // We have a public input unsolved_grid and a private input solved_grid.
    // We want to prove that unsolved_grid is a valid sudoku grid and that it is
    // a solution to solved_grid.
    // this sudoku version for 4*4 grid and it just looks if every row has 1, 2, 3, 4 permutation
    

    // standard proof setup
    let config = CircuitConfig::standard_recursion_config();
    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;
    let mut builder = CircuitBuilder::<F, D>::new(config);
    
    // The unsolved grid.
    let mut unsolved_grid: Vec<plonky2::iop::target::Target> = Vec::new();
    for _ in 0..4 {
        for _ in 0..4 {
            unsolved_grid.push(builder.add_virtual_target());
        }
    }
    for i in 0..4 {
        for j in 0..4 {
            builder.register_public_input(unsolved_grid[i * 4 + j]);
        }
    }

    // The solved grid.
    let mut solved_grid: Vec<plonky2::iop::target::Target> = Vec::new();
    for _ in 0..4 {
        for _ in 0..4 {
            solved_grid.push(builder.add_virtual_target());
        }
    }

    // Assert that the solved grid is a valid sudoku grid.
    for i in 0..4 {
        for j in 0..4 {
            builder.range_check(solved_grid[i * 4 + j], 3);
        }
    }

    // check the solved grid is a valid solution
    for i in 0..4 {
        AllDifferent(&mut builder, solved_grid[i*4..(i+1)*4].to_vec());
    }


    
    // generate circuit data
    let data = builder.build::<C>();
    let mut pw = PartialWitness::<F>::new();
    // Provide initial values.
    for i in 0..4 {
        for j in 0..4 {
            pw.set_target(solved_grid[i * 4 + j], F::from_canonical_u32((change_type(j+i).rem_euclid(4)+1)));
        }
    }
    for i in 0..4 {
        for j in 0..4 {
            if change_type(j+i).rem_euclid(4) == 3 {
                pw.set_target(unsolved_grid[i * 4 + j], F::ZERO);
            }
            else {
                pw.set_target(unsolved_grid[i * 4 + j], F::from_canonical_u32((change_type(j+i).rem_euclid(4)+1)));
            }
        }
    }

    // Generate proof
    let proof = data.prove(pw)?;
    data.verify(proof)?;

    Ok(())
}
/* 
    // Assert that the unsolved grid is a valid sudoku grid.
    for (i, j) in (0..9).flat_map(|i| (i, 0..9)) {
        builder.range_checker(unsolved_grid[i * 9 + j], 1, 9);
    }

    // Assert that solved_grid is a solution to unsolved_grid.
    for (i, j) in (0..9).flat_map(|i| (i, 0..9)) {
        builder.is_equal(solved_grid[i * 9 + j], unsolved_grid[i * 9 + j]);
    }

    // Check rows.
    for i in 0..9 {
        for j in 0..9 {
            builder.contains_all(solved_grid[i * 9 + j], 9);
        }
    }

    // Check columns.
    for i in 0..9 {
        for j in 0..9 {
            builder.contains_all(solved_grid[j * 9 + i], 9);
        }
    }

    // Check submatrices.
    for i in 0..9; i += 3 {
        for j in 0..9; j += 3 {
            for k in 0..3; k++ {
                for l in 0..3; l++ {
                    builder.contains_all(solved_grid[i + k * 3][j + l * 3], 9);
                }
            }
        }
    }

    // generate circuit data
    let data = builder.build::<C>();
    let mut pw = PartialWitness::<F>::new();

    // Provide initial values.
    pw.set_public_input_array(unsolved_grid, [1, 2, 3, 4, 5, 6, 7, 8, 9].repeat(9));
    pw.set_private_input_array(solved_grid, [1, 2, 3, 4, 5, 6, 7, 8, 9].repeat(9));

    // Generate proof
    let proof = data.prove(pw)?;
    data.verify(proof)?;

    Ok(())
    */
