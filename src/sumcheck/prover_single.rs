use super::proof::SumcheckPolynomial;
use crate::{
    poly::{coeffs::CoefficientList, evals::EvaluationsList, multilinear::MultilinearPoint},
    utils::eval_eq,
    whir::statement::Statement,
};
use p3_field::Field;
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSlice,
};

/// Implements the single-round sumcheck protocol for verifying a multilinear polynomial evaluation.
///
/// This struct is responsible for:
/// - Transforming a polynomial from coefficient representation into evaluation form.
/// - Constructing and evaluating weighted constraints.
/// - Computing the sumcheck polynomial, which is a quadratic polynomial in a single variable.
///
/// Given a multilinear polynomial `p(X1, ..., Xn)`, the sumcheck polynomial is computed as:
///
/// \begin{equation}
/// S(X) = \sum p(\beta) \cdot w(\beta) \cdot X
/// \end{equation}
///
/// where:
/// - `\beta` ranges over evaluation points in `{0,1,2}^k` (with `k=1` in this implementation).
/// - `w(\beta)` represents generic weights applied to `p(\beta)`.
/// - The result `S(X)` is a quadratic polynomial in `X`.
///
/// The sumcheck protocol ensures that the claimed sum is correct.
#[derive(Debug)]
pub struct SumcheckSingle<F> {
    /// Evaluations of the polynomial `p(X)`.
    evaluation_of_p: EvaluationsList<F>,
    /// Evaluations of the equality polynomial used for enforcing constraints.
    weights: EvaluationsList<F>,
    /// Accumulated sum incorporating equality constraints.
    sum: F,
}

impl<F> SumcheckSingle<F>
where
    F: Field,
{
    /// Constructs a new `SumcheckSingle` instance from polynomial coefficients.
    ///
    /// This function:
    /// - Converts `coeffs` into evaluation form.
    /// - Initializes an empty constraint table.
    /// - Applies weighted constraints if provided.
    ///
    /// The provided `Statement` encodes constraints that contribute to the final sumcheck equation.
    pub fn new(
        coeffs: CoefficientList<F>,
        statement: &Statement<F>,
        combination_randomness: F,
    ) -> Self {
        let (weights, sum) = statement.combine(combination_randomness);
        Self { evaluation_of_p: coeffs.into(), weights, sum }
    }

    /// Returns the number of variables in the polynomial.
    pub const fn num_variables(&self) -> usize {
        self.evaluation_of_p.num_variables()
    }

    /// Adds new weighted constraints to the polynomial.
    ///
    /// This function updates the weight evaluations and sum by incorporating new constraints.
    ///
    /// Given points `z_i`, weights `ε_i`, and evaluation values `f(z_i)`, it updates:
    ///
    /// \begin{equation}
    /// w(X) = w(X) + \sum \epsilon_i \cdot w_{z_i}(X)
    /// \end{equation}
    ///
    /// and updates the sum as:
    ///
    /// \begin{equation}
    /// S = S + \sum \epsilon_i \cdot f(z_i)
    /// \end{equation}
    ///
    /// where `w_{z_i}(X)` represents the constraint encoding at point `z_i`.
    pub fn add_new_equality(
        &mut self,
        points: &[MultilinearPoint<F>],
        combination_randomness: &[F],
        evaluations: &[F],
    ) {
        assert_eq!(combination_randomness.len(), points.len());
        assert_eq!(combination_randomness.len(), evaluations.len());
        for (point, rand) in points.iter().zip(combination_randomness) {
            // TODO: We might want to do all points simultaneously so we
            // do only a single pass over the data.
            eval_eq(&point.0, self.weights.evals_mut(), *rand);
        }
        // Update the sum
        for (rand, eval) in combination_randomness.iter().zip(evaluations.iter()) {
            self.sum += *rand * *eval;
        }
    }

    /// Computes the sumcheck polynomial `S(X)`, which is quadratic.
    ///
    /// The sumcheck polynomial is given by:
    ///
    /// \begin{equation}
    /// S(X) = \sum p(\beta) \cdot w(\beta) \cdot X
    /// \end{equation}
    ///
    /// where:
    /// - `\beta` represents points in `{0,1,2}^1`.
    /// - `w(\beta)` are the generic weights applied to `p(\beta)`.
    /// - `S(X)` is a quadratic polynomial.
    pub fn compute_sumcheck_polynomial(&self) -> SumcheckPolynomial<F> {
        assert!(self.num_variables() >= 1);

        println!("weights: {:?}", self.weights.evals());

        // Compute the quadratic coefficients using parallel reduction
        let (c0, c2) = self
            .evaluation_of_p
            .evals()
            .par_chunks_exact(2)
            .zip(self.weights.evals().par_chunks_exact(2))
            .map(|(p_at, eq_at)| {
                // Convert evaluations to coefficients for the linear fns p and eq.
                let (p_0, p_1) = (p_at[0], p_at[1] - p_at[0]);
                let (eq_0, eq_1) = (eq_at[0], eq_at[1] - eq_at[0]);

                // Now we need to add the contribution of p(x) * eq(x)
                (p_0 * eq_0, p_1 * eq_1)
            })
            .reduce(|| (F::ZERO, F::ZERO), |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2));

        // Compute the middle coefficient using sum rule: sum = 2 * c0 + c1 + c2
        let c1 = self.sum - c0.double() - c2;

        // Evaluate the quadratic polynomial at 0, 1, 2
        let eval_0 = c0;
        let eval_1 = c0 + c1 + c2;
        let eval_2 = eval_1 + c1 + c2 + c2.double();

        SumcheckPolynomial::new(vec![eval_0, eval_1, eval_2], 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        poly::{coeffs::CoefficientList, multilinear::MultilinearPoint},
        whir::statement::Weights,
    };
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn test_sumcheck_single_initialization() {
        // Polynomial with 2 variables: f(X1, X2) = 1 + 2*X1 + 3*X2 + 4*X1*X2
        let c1 = BabyBear::from_u64(1);
        let c2 = BabyBear::from_u64(2);
        let c3 = BabyBear::from_u64(3);
        let c4 = BabyBear::from_u64(4);

        let coeffs = CoefficientList::new(vec![c1, c2, c3, c4]);
        let statement = Statement::new(2);

        let prover = SumcheckSingle::new(coeffs, &statement, BabyBear::ONE);

        // Expected evaluation table after wavelet transform
        let expected_evaluation_of_p = vec![c1, c1 + c2, c1 + c3, c1 + c2 + c3 + c4];

        assert_eq!(prover.evaluation_of_p.evals(), &expected_evaluation_of_p);
        assert_eq!(prover.weights.evals(), &vec![BabyBear::ZERO; 4]);
        assert_eq!(prover.sum, BabyBear::ZERO);
        assert_eq!(prover.num_variables(), 2);
    }

    #[test]
    fn test_sumcheck_single_one_variable() {
        // Polynomial with 1 variable: f(X1) = 1 + 3*X1
        let c1 = BabyBear::from_u64(1);
        let c2 = BabyBear::from_u64(3);

        // Convert the polynomial into coefficient form
        let coeffs = CoefficientList::new(vec![c1, c2]);

        // Create an empty statement (no equality constraints)
        let statement = Statement::new(1);

        // Instantiate the Sumcheck prover
        let prover = SumcheckSingle::new(coeffs, &statement, BabyBear::ONE);

        // Expected evaluations of the polynomial in evaluation form
        let expected_evaluation_of_p = vec![c1, c1 + c2];

        assert_eq!(prover.evaluation_of_p.evals(), &expected_evaluation_of_p);
        assert_eq!(prover.weights.evals(), &vec![BabyBear::ZERO; 2]);
        assert_eq!(prover.sum, BabyBear::ZERO);
        assert_eq!(prover.num_variables(), 1);
    }

    #[test]
    fn test_sumcheck_single_three_variables() {
        // Polynomial with 3 variables:
        // f(X1, X2, X3) = 1 + 2*X1 + 3*X2 + 4*X1*X2 + 5*X3 + 6*X1*X3 + 7*X2*X3 + 8*X1*X2*X3
        let c1 = BabyBear::from_u64(1);
        let c2 = BabyBear::from_u64(2);
        let c3 = BabyBear::from_u64(3);
        let c4 = BabyBear::from_u64(4);
        let c5 = BabyBear::from_u64(5);
        let c6 = BabyBear::from_u64(6);
        let c7 = BabyBear::from_u64(7);
        let c8 = BabyBear::from_u64(8);

        // Convert the polynomial into coefficient form
        let coeffs = CoefficientList::new(vec![c1, c2, c3, c4, c5, c6, c7, c8]);

        // Create an empty statement (no equality constraints)
        let statement = Statement::new(3);

        // Instantiate the Sumcheck prover
        let prover = SumcheckSingle::new(coeffs, &statement, BabyBear::ONE);

        // Expected evaluations of the polynomial in evaluation form
        let expected_evaluation_of_p = vec![
            c1,
            c1 + c2,
            c1 + c3,
            c1 + c2 + c3 + c4,
            c1 + c5,
            c1 + c2 + c5 + c6,
            c1 + c3 + c5 + c7,
            c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8,
        ];

        assert_eq!(prover.evaluation_of_p.evals(), &expected_evaluation_of_p);
        assert_eq!(prover.weights.evals(), &vec![BabyBear::ZERO; 8]);
        assert_eq!(prover.sum, BabyBear::ZERO);
        assert_eq!(prover.num_variables(), 3);
    }

    #[test]
    fn test_sumcheck_single_with_equality_constraints() {
        // Define a polynomial with 2 variables:
        // f(X1, X2) = 1 + 2*X1 + 3*X2 + 4*X1*X2
        let c1 = BabyBear::from_u64(1);
        let c2 = BabyBear::from_u64(2);
        let c3 = BabyBear::from_u64(3);
        let c4 = BabyBear::from_u64(4);

        // Convert the polynomial into coefficient form
        let coeffs = CoefficientList::new(vec![c1, c2, c3, c4]);

        // Create a statement and introduce an equality constraint at (X1, X2) = (1,0)
        let mut statement = Statement::new(2);
        let point = MultilinearPoint(vec![BabyBear::ONE, BabyBear::ZERO]);
        let weights = Weights::evaluation(point);
        let eval = BabyBear::from_u64(5);
        statement.add_constraint(weights, eval);

        // Instantiate the Sumcheck prover
        let prover = SumcheckSingle::new(coeffs, &statement, BabyBear::ONE);

        // Expected sum update: sum = 5
        assert_eq!(prover.sum, eval);

        // Expected evaluation table after wavelet transform
        let expected_evaluation_of_p = vec![c1, c1 + c2, c1 + c3, c1 + c2 + c3 + c4];
        assert_eq!(prover.evaluation_of_p.evals(), &expected_evaluation_of_p);
        assert_eq!(prover.num_variables(), 2);
    }

    #[test]
    fn test_sumcheck_single_multiple_constraints() {
        // Define a polynomial with 3 variables:
        // f(X1, X2, X3) = c1 + c2*X1 + c3*X2 + c4*X3 + c5*X1*X2 + c6*X1*X3 + c7*X2*X3 + c8*X1*X2*X3
        let c1 = BabyBear::from_u64(1);
        let c2 = BabyBear::from_u64(2);
        let c3 = BabyBear::from_u64(3);
        let c4 = BabyBear::from_u64(4);
        let c5 = BabyBear::from_u64(5);
        let c6 = BabyBear::from_u64(6);
        let c7 = BabyBear::from_u64(7);
        let c8 = BabyBear::from_u64(8);

        // Convert the polynomial into coefficient form
        let coeffs = CoefficientList::new(vec![c1, c2, c3, c4, c5, c6, c7, c8]);

        // Create a statement and introduce multiple equality constraints
        let mut statement = Statement::new(3);

        // Constraints: (X1, X2, X3) = (1,0,1) with weight 2, (0,1,0) with weight 3
        let point1 = MultilinearPoint(vec![BabyBear::ONE, BabyBear::ZERO, BabyBear::ONE]);
        let point2 = MultilinearPoint(vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::ZERO]);

        let weights1 = Weights::evaluation(point1);
        let weights2 = Weights::evaluation(point2);

        let eval1 = BabyBear::from_u64(5);
        let eval2 = BabyBear::from_u64(4);

        statement.add_constraint(weights1, eval1);
        statement.add_constraint(weights2, eval2);

        // Instantiate the Sumcheck prover
        let prover = SumcheckSingle::new(coeffs, &statement, BabyBear::ONE);

        // Expected sum update: sum = (5) + (4)
        let expected_sum = eval1 + eval2;
        assert_eq!(prover.sum, expected_sum);
    }

    #[test]
    fn test_compute_sumcheck_polynomial_basic() {
        // Polynomial with 2 variables: f(X1, X2) = c1 + c2*X1 + c3*X2 + c4*X1*X2
        let c1 = BabyBear::from_u64(1);
        let c2 = BabyBear::from_u64(2);
        let c3 = BabyBear::from_u64(3);
        let c4 = BabyBear::from_u64(4);

        // Convert the polynomial into coefficient form
        let coeffs = CoefficientList::new(vec![c1, c2, c3, c4]);

        // Create an empty statement (no constraints)
        let statement = Statement::new(2);

        // Instantiate the Sumcheck prover
        let prover = SumcheckSingle::new(coeffs, &statement, BabyBear::ONE);
        let sumcheck_poly = prover.compute_sumcheck_polynomial();

        // Since no equality constraints, sumcheck_poly should be **zero**
        let expected_evaluations = vec![BabyBear::ZERO; 3];
        assert_eq!(sumcheck_poly.evaluations(), &expected_evaluations);
    }

    #[test]
    fn test_compute_sumcheck_polynomial_with_equality_constraints() {
        // Define a multilinear polynomial with two variables:
        // f(X1, X2) = c1 + c2*X1 + c3*X2 + c4*X1*X2
        // This polynomial is represented in coefficient form.
        let c1 = BabyBear::from_u64(1);
        let c2 = BabyBear::from_u64(2);
        let c3 = BabyBear::from_u64(3);
        let c4 = BabyBear::from_u64(4);

        // Convert the polynomial into coefficient list representation
        let coeffs = CoefficientList::new(vec![c1, c2, c3, c4]);

        // Create a statement and introduce an equality constraint at (X1, X2) = (1,0)
        // The constraint enforces that f(1,0) must evaluate to 5 with weight 2.
        let mut statement = Statement::new(2);
        let point = MultilinearPoint(vec![BabyBear::ONE, BabyBear::ZERO]);
        let weights = Weights::evaluation(point);
        let eval = BabyBear::from_u64(5);
        statement.add_constraint(weights, eval);

        // Instantiate the Sumcheck prover with the polynomial and equality constraints
        let prover = SumcheckSingle::new(coeffs, &statement, BabyBear::ONE);
        let sumcheck_poly = prover.compute_sumcheck_polynomial();

        // The constraint directly contributes to the sum, hence sum = 5
        assert_eq!(prover.sum, eval);

        // Compute the polynomial evaluations at the four possible binary inputs
        let ep_00 = c1; // f(0,0) = c1
        let ep_01 = c1 + c2; // f(0,1) = c1 + c2
        let ep_10 = c1 + c3; // f(1,0) = c1 + c3
        let ep_11 = c1 + c3 + c2 + c4; // f(1,1) = c1 + c3 + c2 + c4

        // Compute the evaluations of the equality constraint polynomial at each binary input
        // Given that the constraint is at (1,0) with weight 2, the equality function is:
        //
        // \begin{equation}
        // eq(X1, X2) = 2 * (X1 - 1) * (X2 - 0)
        // \end{equation}
        let f_00 = BabyBear::ZERO; // eq(0,0) = 0
        let f_01 = BabyBear::ZERO; // eq(0,1) = 0
        let f_10 = BabyBear::ONE; // eq(1,0) = 1
        let f_11 = BabyBear::ZERO; // eq(1,1) = 0

        // Compute the coefficients of the sumcheck polynomial S(X)
        let e0 = ep_00 * f_00 + ep_10 * f_10; // Constant term (X = 0)
        let e2 = (ep_01 - ep_00) * (f_01 - f_00) + (ep_11 - ep_10) * (f_11 - f_10); // Quadratic coefficient
        let e1 = prover.sum - e0.double() - e2; // Middle coefficient using sum rule

        // Compute the evaluations of the sumcheck polynomial at X ∈ {0,1,2}
        let eval_0 = e0;
        let eval_1 = e0 + e1 + e2;
        let eval_2 = eval_1 + e1 + e2 + e2.double();
        let expected_evaluations = vec![eval_0, eval_1, eval_2];

        // Ensure that the computed sumcheck polynomial matches expectations
        assert_eq!(sumcheck_poly.evaluations(), &expected_evaluations);
    }

    #[test]
    fn test_compute_sumcheck_polynomial_with_equality_constraints_3vars() {
        // Define a multilinear polynomial with three variables:
        // f(X1, X2, X3) = c1 + c2*X1 + c3*X2 + c4*X3 + c5*X1*X2 + c6*X1*X3 + c7*X2*X3 + c8*X1*X2*X3
        let c1 = BabyBear::from_u64(1);
        let c2 = BabyBear::from_u64(2);
        let c3 = BabyBear::from_u64(3);
        let c4 = BabyBear::from_u64(4);
        let c5 = BabyBear::from_u64(5);
        let c6 = BabyBear::from_u64(6);
        let c7 = BabyBear::from_u64(7);
        let c8 = BabyBear::from_u64(8);

        // Convert the polynomial into coefficient form
        let coeffs = CoefficientList::new(vec![c1, c2, c3, c4, c5, c6, c7, c8]);

        // Create a statement and introduce an equality constraint at (X1, X2, X3) = (1,0,1)
        let mut statement = Statement::new(3);
        let point = MultilinearPoint(vec![BabyBear::ONE, BabyBear::ZERO, BabyBear::ONE]);
        let weights = Weights::evaluation(point);
        let eval = BabyBear::from_u64(5);
        statement.add_constraint(weights, eval);

        // Instantiate the Sumcheck prover with the polynomial and equality constraints
        let prover = SumcheckSingle::new(coeffs, &statement, BabyBear::ONE);
        let sumcheck_poly = prover.compute_sumcheck_polynomial();

        // Expected sum update: sum = 5
        assert_eq!(prover.sum, eval);

        // Compute polynomial evaluations at the eight possible binary inputs
        let ep_000 = c1; // f(0,0,0)
        let ep_001 = c1 + c2; // f(0,0,1)
        let ep_010 = c1 + c3; // f(0,1,0)
        let ep_011 = c1 + c2 + c3 + c4; // f(0,1,1)
        let ep_100 = c1 + c5; // f(1,0,0)
        let ep_101 = c1 + c2 + c5 + c6; // f(1,0,1)
        let ep_110 = c1 + c3 + c5 + c7; // f(1,1,0)
        let ep_111 = c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8; // f(1,1,1)

        // Compute the evaluations of the equality constraint polynomial at each binary input
        // Given that the constraint is at (1,0,1) with weight 2, the equality function is:
        //
        // \begin{equation}
        // eq(X1, X2, X3) = 2 * (X1 - 1) * (X2 - 0) * (X3 - 1)
        // \end{equation}
        let f_000 = BabyBear::ZERO; // eq(0,0,0) = 0
        let f_001 = BabyBear::ZERO; // eq(0,0,1) = 0
        let f_010 = BabyBear::ZERO; // eq(0,1,0) = 0
        let f_011 = BabyBear::ZERO; // eq(0,1,1) = 0
        let f_100 = BabyBear::ZERO; // eq(1,0,0) = 0
        let f_101 = BabyBear::ONE; // eq(1,0,1) = 1
        let f_110 = BabyBear::ZERO; // eq(1,1,0) = 0
        let f_111 = BabyBear::ZERO; // eq(1,1,1) = 0

        // Compute the coefficients of the sumcheck polynomial S(X)
        let e0 = ep_000 * f_000 + ep_010 * f_010 + ep_100 * f_100 + ep_110 * f_110; // Contribution at X = 0
        let e2 = (ep_001 - ep_000) * (f_001 - f_000) +
            (ep_011 - ep_010) * (f_011 - f_010) +
            (ep_101 - ep_100) * (f_101 - f_100) +
            (ep_111 - ep_110) * (f_111 - f_110); // Quadratic coefficient
        let e1 = prover.sum - e0.double() - e2; // Middle coefficient using sum rule

        // Compute sumcheck polynomial evaluations at {0,1,2}
        let eval_0 = e0;
        let eval_1 = e0 + e1 + e2;
        let eval_2 = eval_1 + e1 + e2 + e2.double();
        let expected_evaluations = vec![eval_0, eval_1, eval_2];

        // Assert that computed sumcheck polynomial matches expectations
        assert_eq!(sumcheck_poly.evaluations(), &expected_evaluations);
    }
}
