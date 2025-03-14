use crate::prf::PRF;
use ark_ff::Field;
use ark_r1cs_std::prelude::*;
use ark_relations::gr1cs::{Namespace, SynthesisError};
use ark_std::fmt::Debug;
#[cfg(not(feature = "std"))]
use ark_std::vec::Vec;

pub trait PRFGadget<P: PRF, F: Field> {
    type OutputVar: EqGadget<F>
        + ToBytesGadget<F>
        + AllocVar<P::Output, F>
        + GR1CSVar<F, Value = P::Output>
        + Clone
        + Debug;

    fn new_seed(cs: impl Into<Namespace<F>>, seed: &P::Seed) -> Vec<UInt8<F>>;

    fn evaluate(seed: &[UInt8<F>], input: &[UInt8<F>]) -> Result<Self::OutputVar, SynthesisError>;
}
