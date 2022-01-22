use ark_ff::{BitIteratorLE, PrimeField};
use ark_nonnative_field::NonNativeFieldVar;
use ark_poly::Polynomial;
use ark_poly::{polynomial::univariate::DensePolynomial, UVPolynomial};
use ark_r1cs_std::{
    alloc::AllocVar, eq::EqGadget, fields::fp::FpVar,
    poly::polynomial::univariate::dense::DensePolynomialVar,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

pub struct PolyEvaluator<F: PrimeField> {
    poly: DensePolynomial<F>,
    evals: Vec<F>,
    results: Vec<F>,
}

impl<F> PolyEvaluator<F>
where
    F: PrimeField,
{
    // TODO make evaluations points simply (1...n) and put n as public input
    pub fn new(coeffs: Vec<F>, evals: Vec<F>) -> Self {
        let poly = DensePolynomial::from_coefficients_vec(coeffs);
        let res = evals.iter().map(|xi| poly.evaluate(xi)).collect::<Vec<_>>();
        Self {
            poly,
            evals,
            results: res,
        }
    }

    pub fn check_evaluations<F2: PrimeField>(
        self,
        cs: ConstraintSystemRef<F2>,
    ) -> Result<(), SynthesisError> {
        let coeff_vars = self
            .poly
            .coeffs
            .iter()
            .map(|ci| {
                NonNativeFieldVar::<F, F2>::new_input(ark_relations::ns!(cs, "coefi"), || Ok(ci))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let evals = self
            .evals
            .iter()
            .map(|e| {
                NonNativeFieldVar::<F, F2>::new_witness(ark_relations::ns!(cs, "xi"), || Ok(e))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let results = self
            .results
            .iter()
            .map(|r| {
                NonNativeFieldVar::<F, F2>::new_witness(ark_relations::ns!(cs, "resi"), || Ok(r))
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (xi, yi) in evals.iter().zip(results.iter()) {
            let exp = poly_eval(&coeff_vars, xi)?;
            yi.enforce_equal(&exp)?;
        }
        Ok(())
    }
}

fn poly_eval<F: PrimeField, F2: PrimeField>(
    coeffs: &[NonNativeFieldVar<F, F2>],
    eval: &NonNativeFieldVar<F, F2>,
) -> Result<NonNativeFieldVar<F, F2>, SynthesisError> {
    let mut r = coeffs[coeffs.len() - 1].clone();
    for ci in coeffs.iter().rev().skip(1) {
        let rr = r * eval;
        r = &rr + ci;
    }
    Ok(r)
}

impl<F> ConstraintSynthesizer<F> for PolyEvaluator<F>
where
    F: PrimeField,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        self.check_evaluations(cs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_377::{constraints::*, *};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    // test eval_nonnative::tests::nonnative_poly_eval has been running for over 60 seconds
    // Degree of polynomial: 50
    // Number of evaluation points: 99
    // num constraints: 3387483
    // test eval_nonnative::tests::nonnative_poly_eval ... ok

    #[test]
    fn nonnative_poly_eval() {
        let degree = 50;
        let n = degree * 2 - 1;
        let mut rng = ark_std::test_rng();
        let coeffs = (0..degree + 1)
            .map(|_| Fr::rand(&mut rng))
            .collect::<Vec<_>>();
        let evals = (0..n).map(|i| Fr::from(i + 1)).collect::<Vec<_>>();
        let pe = PolyEvaluator::new(coeffs, evals);
        let cs = ConstraintSystem::<Fr>::new_ref();
        pe.generate_constraints(cs.clone()).unwrap();
        println!("Degree of polynomial: {}", degree);
        println!("Number of evaluation points: {}", n);
        println!("num constraints: {}", cs.num_constraints());
        assert!(cs.is_satisfied().unwrap());
    }
}
