use ark_ff::{BitIteratorLE, PrimeField};
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
    pub results: Vec<F>,
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
    pub fn public_inputs(&self) -> Vec<F> {
        let mut pubs = self.poly.coeffs.clone();
        pubs.append(&mut self.evals.clone());
        pubs.append(&mut self.results.clone());
        pubs
    }
    pub fn check_evaluations(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let coeff_vars = self
            .poly
            .coeffs
            .iter()
            .map(|ci| FpVar::new_input(ark_relations::ns!(cs, "coefi"), || Ok(ci)))
            .collect::<Result<Vec<_>, _>>()?;
        let poly_var = DensePolynomialVar::from_coefficients_vec(coeff_vars);
        // TODO - avoid that by just doing a range from 1 ... n
        let evals = self
            .evals
            .iter()
            .map(|e| FpVar::new_input(ark_relations::ns!(cs, "xi"), || Ok(e)))
            .collect::<Result<Vec<_>, _>>()?;
        let results = self
            .results
            .iter()
            .map(|r| FpVar::new_input(ark_relations::ns!(cs, "resi"), || Ok(r)))
            .collect::<Result<Vec<_>, _>>()?;
        for (xi, yi) in evals.iter().zip(results.iter()) {
            let exp = poly_var.evaluate(xi)?;
            yi.enforce_equal(&exp)?;
        }
        Ok(())
    }
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

    #[test]
    fn poly_eval() {
        let degree = 500;
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