use crate::commitment::CommitmentScheme;
use ark_ff::Field;
use ark_r1cs_std::prelude::*;
use ark_relations::gr1cs::SynthesisError;
use ark_std::fmt::Debug;

pub trait CommitmentGadget<C: CommitmentScheme, ConstraintF: Field> {
    type OutputVar: EqGadget<ConstraintF>
        + ToBytesGadget<ConstraintF>
        + AllocVar<C::Output, ConstraintF>
        + GR1CSVar<ConstraintF>
        + Clone
        + Sized
        + Debug;
    type ParametersVar: AllocVar<C::Parameters, ConstraintF> + Clone;
    type RandomnessVar: AllocVar<C::Randomness, ConstraintF> + Clone;

    fn commit(
        parameters: &Self::ParametersVar,
        input: &[UInt8<ConstraintF>],
        r: &Self::RandomnessVar,
    ) -> Result<Self::OutputVar, SynthesisError>;
}
