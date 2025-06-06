use crate::encryption::{
    elgamal::{Ciphertext, ElGamal, Parameters, Plaintext, PublicKey, Randomness},
    AsymmetricEncryptionGadget,
};
use ark_ec::CurveGroup;
use ark_ff::{
    fields::{Field, PrimeField},
    Zero,
};
use ark_r1cs_std::prelude::*;
use ark_relations::gr1cs::{Namespace, SynthesisError};
use ark_serialize::CanonicalSerialize;
#[cfg(not(feature = "std"))]
use ark_std::vec::Vec;
use ark_std::{borrow::Borrow, marker::PhantomData};

pub type ConstraintF<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

#[derive(Clone, Debug)]
pub struct RandomnessVar<F: Field>(Vec<UInt8<F>>);

impl<C, F> AllocVar<Randomness<C>, F> for RandomnessVar<F>
where
    C: CurveGroup,
    F: PrimeField,
{
    fn new_variable<T: Borrow<Randomness<C>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let mut r = Vec::new();
        let _ = &f()
            .map(|b| b.borrow().0)
            .unwrap_or(C::ScalarField::zero())
            .serialize_compressed(&mut r)
            .unwrap();
        match mode {
            AllocationMode::Constant => Ok(Self(UInt8::constant_vec(&r))),
            AllocationMode::Input => UInt8::new_input_vec(cs, &r).map(Self),
            AllocationMode::Witness => UInt8::new_witness_vec(cs, &r).map(Self),
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "C: CurveGroup, GG: CurveVar<C, ConstraintF<C>>"))]
pub struct ParametersVar<C: CurveGroup, GG: CurveVar<C, ConstraintF<C>>>
where
    for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
{
    generator: GG,
    #[doc(hidden)]
    _curve: PhantomData<C>,
}

impl<C, GG> AllocVar<Parameters<C>, ConstraintF<C>> for ParametersVar<C, GG>
where
    C: CurveGroup,
    GG: CurveVar<C, ConstraintF<C>>,
    for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
{
    fn new_variable<T: Borrow<Parameters<C>>>(
        cs: impl Into<Namespace<ConstraintF<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let generator = GG::new_variable(cs, || f().map(|g| g.borrow().generator), mode)?;
        Ok(Self {
            generator,
            _curve: PhantomData,
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "C: CurveGroup, GG: CurveVar<C, ConstraintF<C>>"))]
pub struct PlaintextVar<C: CurveGroup, GG: CurveVar<C, ConstraintF<C>>>
where
    for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
{
    pub plaintext: GG,
    #[doc(hidden)]
    _curve: PhantomData<C>,
}

impl<C, GG> AllocVar<Plaintext<C>, ConstraintF<C>> for PlaintextVar<C, GG>
where
    C: CurveGroup,
    GG: CurveVar<C, ConstraintF<C>>,
    for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
{
    fn new_variable<T: Borrow<Plaintext<C>>>(
        cs: impl Into<Namespace<ConstraintF<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let plaintext = GG::new_variable(cs, f, mode)?;
        Ok(Self {
            plaintext,
            _curve: PhantomData,
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "C: CurveGroup, GG: CurveVar<C, ConstraintF<C>>"))]
pub struct PublicKeyVar<C: CurveGroup, GG: CurveVar<C, ConstraintF<C>>>
where
    for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
{
    pub pk: GG,
    #[doc(hidden)]
    _curve: PhantomData<C>,
}

impl<C, GG> AllocVar<PublicKey<C>, ConstraintF<C>> for PublicKeyVar<C, GG>
where
    C: CurveGroup,
    GG: CurveVar<C, ConstraintF<C>>,
    for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
{
    fn new_variable<T: Borrow<PublicKey<C>>>(
        cs: impl Into<Namespace<ConstraintF<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let pk = GG::new_variable(cs, f, mode)?;
        Ok(Self {
            pk,
            _curve: PhantomData,
        })
    }
}

#[derive(Derivative, Debug)]
#[derivative(Clone(bound = "C: CurveGroup, GG: CurveVar<C, ConstraintF<C>>"))]
pub struct OutputVar<C: CurveGroup, GG: CurveVar<C, ConstraintF<C>>>
where
    for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
{
    pub c1: GG,
    pub c2: GG,
    #[doc(hidden)]
    _curve: PhantomData<C>,
}

impl<C, GG> AllocVar<Ciphertext<C>, ConstraintF<C>> for OutputVar<C, GG>
where
    C: CurveGroup,
    GG: CurveVar<C, ConstraintF<C>>,
    for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
{
    fn new_variable<T: Borrow<Ciphertext<C>>>(
        cs: impl Into<Namespace<ConstraintF<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let prep = f().map(|g| *g.borrow());
        let c1 = GG::new_variable(cs.clone(), || prep.map(|g| g.0), mode)?;
        let c2 = GG::new_variable(cs.clone(), || prep.map(|g| g.1), mode)?;
        Ok(Self {
            c1,
            c2,
            _curve: PhantomData,
        })
    }
}

impl<C, GC> EqGadget<ConstraintF<C>> for OutputVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, ConstraintF<C>>,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    #[inline]
    fn is_eq(&self, other: &Self) -> Result<Boolean<ConstraintF<C>>, SynthesisError> {
        Ok(self.c1.is_eq(&other.c1)? & &self.c2.is_eq(&other.c2)?)
    }
}

pub struct ElGamalEncGadget<C: CurveGroup, GG: CurveVar<C, ConstraintF<C>>>
where
    for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
{
    #[doc(hidden)]
    _curve: PhantomData<*const C>,
    _group_var: PhantomData<*const GG>,
}

impl<C, GG> AsymmetricEncryptionGadget<ElGamal<C>, ConstraintF<C>> for ElGamalEncGadget<C, GG>
where
    C: CurveGroup,
    GG: CurveVar<C, ConstraintF<C>>,
    for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
    ConstraintF<C>: PrimeField,
{
    type OutputVar = OutputVar<C, GG>;
    type ParametersVar = ParametersVar<C, GG>;
    type PlaintextVar = PlaintextVar<C, GG>;
    type PublicKeyVar = PublicKeyVar<C, GG>;
    type RandomnessVar = RandomnessVar<ConstraintF<C>>;

    fn encrypt(
        parameters: &Self::ParametersVar,
        message: &Self::PlaintextVar,
        randomness: &Self::RandomnessVar,
        public_key: &Self::PublicKeyVar,
    ) -> Result<Self::OutputVar, SynthesisError> {
        // flatten randomness to little-endian bit vector
        let randomness = randomness
            .0
            .iter()
            .flat_map(|b| b.to_bits_le().unwrap())
            .collect::<Vec<_>>();

        // compute s = randomness*pk
        let s = public_key.pk.clone().scalar_mul_le(randomness.iter())?;

        // compute c1 = randomness*generator
        let c1 = parameters
            .generator
            .clone()
            .scalar_mul_le(randomness.iter())?;

        // compute c2 = m + s
        let c2 = message.plaintext.clone() + s;

        Ok(Self::OutputVar {
            c1,
            c2,
            _curve: PhantomData,
        })
    }
}

#[cfg(test)]
mod test {
    use crate::encryption::constraints::AsymmetricEncryptionGadget;
    use ark_std::{test_rng, UniformRand};

    use ark_ed_on_bls12_381::{constraints::EdwardsVar, EdwardsProjective as JubJub, Fq};

    use crate::encryption::elgamal::{constraints::ElGamalEncGadget, ElGamal, Randomness};
    use crate::encryption::AsymmetricEncryptionScheme;
    use ark_r1cs_std::prelude::*;
    use ark_relations::gr1cs::ConstraintSystem;

    #[test]
    fn test_elgamal_gadget() {
        let rng = &mut test_rng();

        type MyEnc = ElGamal<JubJub>;
        type MyGadget = ElGamalEncGadget<JubJub, EdwardsVar>;

        // compute primitive result
        let parameters = MyEnc::setup(rng).unwrap();
        let (pk, _) = MyEnc::keygen(&parameters, rng).unwrap();
        let msg = JubJub::rand(rng).into();
        let randomness = Randomness::rand(rng);
        let primitive_result = MyEnc::encrypt(&parameters, &pk, &msg, &randomness).unwrap();

        // construct constraint system
        let cs = ConstraintSystem::<Fq>::new_ref();
        let randomness_var =
            <MyGadget as AsymmetricEncryptionGadget<MyEnc, Fq>>::RandomnessVar::new_witness(
                ark_relations::ns!(cs, "gadget_randomness"),
                || Ok(&randomness),
            )
            .unwrap();
        let parameters_var =
            <MyGadget as AsymmetricEncryptionGadget<MyEnc, Fq>>::ParametersVar::new_constant(
                ark_relations::ns!(cs, "gadget_parameters"),
                &parameters,
            )
            .unwrap();
        let msg_var =
            <MyGadget as AsymmetricEncryptionGadget<MyEnc, Fq>>::PlaintextVar::new_witness(
                ark_relations::ns!(cs, "gadget_message"),
                || Ok(&msg),
            )
            .unwrap();
        let pk_var =
            <MyGadget as AsymmetricEncryptionGadget<MyEnc, Fq>>::PublicKeyVar::new_witness(
                ark_relations::ns!(cs, "gadget_public_key"),
                || Ok(&pk),
            )
            .unwrap();

        // use gadget
        let result_var =
            MyGadget::encrypt(&parameters_var, &msg_var, &randomness_var, &pk_var).unwrap();

        // check that result equals expected ciphertext in the constraint system
        let expected_var =
            <MyGadget as AsymmetricEncryptionGadget<MyEnc, Fq>>::OutputVar::new_input(
                ark_relations::ns!(cs, "gadget_expected"),
                || Ok(&primitive_result),
            )
            .unwrap();
        expected_var.enforce_equal(&result_var).unwrap();

        assert_eq!(primitive_result.0, result_var.c1.value().unwrap());
        assert_eq!(primitive_result.1, result_var.c2.value().unwrap());
        assert!(cs.is_satisfied().unwrap());
    }
}
