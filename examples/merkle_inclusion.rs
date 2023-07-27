
use plonky2::{
    field::{goldilocks_field::GoldilocksField, types::Field},
    hash::{merkle_tree::MerkleTree, merkle_proofs::verify_merkle_proof_to_cap},
    hash::poseidon::PoseidonHash
};
use anyhow::{Result, Ok};

fn main() -> Result<()> {
    // standard proof setup
    type F = GoldilocksField;
    type H = PoseidonHash;

    // Generate some random data for the leaves of the Merkle tree.
    let leaves: Vec<Vec<F>> = vec![
        // add random elements of F here
        vec![F::ONE],
        vec![F::ONE],
        vec![F::ONE],
        vec![F::ONE]
    ];

    // Choose the height of the Merkle cap. It should be less than or equal to log2 of the number of leaves.
    let cap_height = 2; // Choose a suitable value here.

    // Create a new Merkle tree.
    let merkle_tree: MerkleTree<GoldilocksField, PoseidonHash> = MerkleTree::<F, H>::new(leaves.clone(), cap_height);

    // Choose a leaf index for which you want to generate a Merkle proof.
    let leaf_index = 0; // Choose the leaf index here.

    // Generate the Merkle proof for the chosen leaf index.
    let proof = merkle_tree.prove(leaf_index);
    verify_merkle_proof_to_cap::<F, H>(leaves[leaf_index].clone(), leaf_index, &merkle_tree.cap, &proof)?;
    Ok(())
}
