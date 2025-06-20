pub use crate::crh::injective_map::InjectiveMap;
use crate::{
    commitment::{pedersen, CommitmentScheme},
    Error,
};
use ark_ec::CurveGroup;
use ark_std::{marker::PhantomData, rand::Rng};

#[cfg(feature = "constraints")]
pub mod constraints;

pub struct PedersenCommCompressor<C: CurveGroup, I: InjectiveMap<C>, W: pedersen::Window> {
    _group: PhantomData<C>,
    _compressor: PhantomData<I>,
    _comm: pedersen::Commitment<C, W>,
}

impl<C: CurveGroup, I: InjectiveMap<C>, W: pedersen::Window> CommitmentScheme
    for PedersenCommCompressor<C, I, W>
{
    type Output = I::Output;
    type Parameters = pedersen::Parameters<C>;
    type Randomness = pedersen::Randomness<C>;

    fn setup<R: Rng>(rng: &mut R) -> Result<Self::Parameters, Error> {
        let time = start_timer!(|| format!("PedersenCompressor::Setup"));
        let params = pedersen::Commitment::<C, W>::setup(rng);
        end_timer!(time);
        params
    }

    fn commit(
        parameters: &Self::Parameters,
        input: &[u8],
        randomness: &Self::Randomness,
    ) -> Result<Self::Output, Error> {
        let eval_time = start_timer!(|| "PedersenCompressor::Eval");
        let result = I::injective_map(&pedersen::Commitment::<C, W>::commit(
            parameters, input, randomness,
        )?)?;
        end_timer!(eval_time);
        Ok(result)
    }
}
