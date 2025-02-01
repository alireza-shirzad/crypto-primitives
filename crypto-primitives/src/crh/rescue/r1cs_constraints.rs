use ark_ff::PrimeField;



const RESCUE_ROUNDS: usize = 12;

/// This is our demo circuit for proving knowledge of the
/// preimage of a Rescue hash invocation.
#[derive(Clone)]
struct RescueDemo<F: PrimeField + ark_ff::PrimeField> {
    input: Option<Vec<F>>,
    image: Option<F>,
    config: RescueConfig<F>,
    N: usize,
}

pub fn create_test_rescue_parameter<F: PrimeField + ark_ff::PrimeField>(
    rng: &mut impl Rng,
) -> RescueConfig<F> {
    let mut mds = vec![vec![]; 4];
    for i in 0..4 {
        for _ in 0..4 {
            mds[i].push(F::rand(rng));
        }
    }

    let mut ark = vec![vec![]; 25];
    for i in 0..(2 * RESCUE_ROUNDS + 1) {
        for _ in 0..4 {
            ark[i].push(F::rand(rng));
        }
    }
    let alpha_inv: BigUint = BigUint::from_str(
        "20974350070050476191779096203274386335076221000211055129041463479975432473805",
    )
    .unwrap();
    let params = RescueConfig::<F>::new(RESCUE_ROUNDS, 5, alpha_inv, mds, ark, 3, 1);
    params
}

impl<F: PrimeField + ark_ff::PrimeField + rescue_gr1cs::sponge::Absorb> ConstraintSynthesizer<F>
    for RescueDemo<F>
{
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        cs.clone().register_predicate(
            gr1cs::MUL,
            LocalPredicate::new(
                3,
                gr1cs::predicate::LocalPredicateType::Polynomial(
                    gr1cs::polynomial::Polynomial::new(
                        3,
                        vec![(F::ONE, vec![1, 1, 0]), (F::ZERO - F::ONE, vec![0, 0, 1])],
                    )
                    .unwrap(),
                ),
            ),
        );


        let params_g =
            CRHParametersVar::<F>::new_witness(cs.clone(), || Ok(self.config.clone())).unwrap();

        for _ in 0..self.N {
            let mut input_g = Vec::new();

            for elem in self
                .input
                .clone()
                .ok_or(SynthesisError::AssignmentMissing)
                .unwrap()
            {
                input_g.push(FpVar::new_witness(cs.clone(), || Ok(elem)).unwrap());
            }

            let crh_a_g: FpVar<F> = CRHGadget::<F>::evaluate(&params_g, &input_g).unwrap();
            let image_instance: FpVar<F> = FpVar::new_input(cs.clone(), || {
                Ok(self.image.ok_or(SynthesisError::AssignmentMissing).unwrap())
            })
            .unwrap();
            crh_a_g.enforce_equal(&image_instance);
        }
        Ok(())
    }
}


#[test]
fn test_rescue() {

    const N: usize = 100;
    // We're going to use the Groth16 proving system.


    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    let config = create_test_rescue_parameter(&mut rng);

    // Generate a random preimage and compute the image
    let mut input = Vec::new();
    for _ in 0..9 {
        input.push(Fr::rand(&mut rng));
    }
    let expected_image = CRH::<Fr>::evaluate(&config, input.clone()).unwrap();

    let c = RescueDemo::<Fr> {
        input: Some(input.clone()),
        image: Some(expected_image),
        config: config.clone(),
        N
    };

    ///////////////////////////////////////////////////////////////////////////////////
    // Create parameters for our circuit
    println!("Creating SRS...");
    let mut setup_time: Duration = Duration::new(0, 0);

    let start = Instant::now();

    let (pk, vk) = { Varuna::<Bls12_381>::setup(&mut rng, c.clone()) };

    setup_time += start.elapsed();
    std::println!("Setup time = {}", setup_time.as_millis());
    ///////////////////////////////////////////////
    // Creating the proof

    println!("Creating proofs...");

    let mut total_proving: Duration = Duration::new(0, 0);

    let start = Instant::now();

    // Create a groth16 proof with our parameters.
    let proof = Varuna::<Bls12_381>::prove(&mut rng, c, pk);
    total_proving += start.elapsed();

    std::println!("Totall Prover time = {}", total_proving.as_millis());

    ///////////////////////////////////////////////
    // Verifying the proof
    let mut total_verifying: Duration = Duration::new(0, 0);
    let start = Instant::now();
    assert!(Varuna::<Bls12_381>::verify(
        &mut rng,
        proof,
        vk,
        &[expected_image;N]
    ));

    // proof.write(&mut proof_vec).unwrap();

    // let proof = Proof::read(&proof_vec[..]).unwrap();
    // Check the proof

    total_verifying += start.elapsed();
}
