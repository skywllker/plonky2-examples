
use plonky2::{
    field::{goldilocks_field::GoldilocksField, types::Field},
    hash::{merkle_tree::MerkleTree, merkle_proofs::verify_merkle_proof_to_cap, hash_types::RichField},
    hash::{poseidon::PoseidonHash, merkle_tree::MerkleCap, merkle_proofs::MerkleProof}, plonk::config::Hasher
};
use anyhow::{Result, Ok, ensure};

// usage of merkle tree library very basicly
// can be used as general layer of how to use merkle tree

pub fn deneme<F: RichField, H: Hasher<F>>(
    leaf_data: Vec<F>,
    leaf_index: usize,
    merkle_cap: &MerkleCap<F, H>,
    proof: &MerkleProof<F, H>,
) -> Result<()> {
    
    let mut index = leaf_index;
    let mut current_digest = H::hash_or_noop(&leaf_data);
    for &sibling_digest in proof.siblings.iter() {
        println!("xx {:#?} ", sibling_digest);
        let bit = index & 1;
        index >>= 1;
        current_digest = if bit == 1 {
            H::two_to_one(sibling_digest, current_digest)
        } else {
            H::two_to_one(current_digest, sibling_digest)
        }
    }
    println!("xx {:#?} ", current_digest);

    ensure!(
        current_digest == merkle_cap.0[index],
        "Invalid Merkle proof."
    );
    Ok(())
}
pub fn root<F: RichField, H: Hasher<F>>(
    merkle_cap: &MerkleCap<F, H>,
) -> H::Hash {
    let mut new_cap = merkle_cap.clone();
    for i in 0..2 {
        let left = new_cap.0[2*i];
        let right = new_cap.0[2*i+1];
        new_cap.0[i] = H::two_to_one(left, right);
    }
    for i in 0..1 {
        let left = new_cap.0[2*i];
        let right = new_cap.0[2*i+1];
        new_cap.0[i] = H::two_to_one(left, right);
    }
    return new_cap.0[0];

}
fn main() -> Result<()> {
    // standard proof setup
    type F = GoldilocksField;
    type H = PoseidonHash;

    // Generate some random data for the leaves of the Merkle tree.
    let leaves: Vec<Vec<F>> = 
    [[F::ONE, F::ZERO, F::ZERO, F::ZERO].to_vec(),
    [F::ZERO, F::ONE, F::ZERO, F::ZERO].to_vec(),
    [F::ZERO, F::ZERO, F::ONE, F::ZERO].to_vec(),
    [F::ZERO, F::ZERO, F::ZERO, F::ONE].to_vec()].to_vec();

    // Choose the height of the Merkle cap. It should be less than or equal to log2 of the number of leaves.
    let cap_height = 2; // Choose a suitable value here.

    // Create a new Merkle tree.
    let merkle_tree: MerkleTree<GoldilocksField, PoseidonHash> = MerkleTree::<F, H>::new(leaves.clone(), cap_height);

    // Choose a leaf index for which you want to generate a Merkle proof.
    let leaf_index = 0; // Choose the leaf index here.

    // Generate the Merkle proof for the chosen leaf index.
    let proof = merkle_tree.prove(leaf_index);
    println!("ROOT {:#?} ", root(&merkle_tree.cap));
    deneme::<F, H>(leaves[leaf_index].clone(), leaf_index, &merkle_tree.cap, &proof)?;
    Ok(())
}
