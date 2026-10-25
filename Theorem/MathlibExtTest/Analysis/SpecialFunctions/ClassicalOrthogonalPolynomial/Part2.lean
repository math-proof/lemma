/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ClassicalOrthogonalPolynomial.lean -/


import Structure.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic
import Def.MathlibExtTest.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial


namespace MetaMathlibExt

open MeasureTheory Set Real

open scoped NNReal

theorem monicChebyshev_monic (n : ℕ) : (monicChebyshev n).Monic := by
  exact Polynomial.monic_mul_leadingCoeff_inv (Polynomial.Chebyshev.T_ne_zero ℝ n)

theorem monicChebyshev_natDegree (n : ℕ) : (monicChebyshev n).natDegree = n := by
  rw [monicChebyshev, Polynomial.natDegree_mul_C]
  · simp
  · rw [Polynomial.Chebyshev.leadingCoeff_T]
    exact inv_ne_zero (pow_ne_zero _ (by norm_num))

theorem monicChebyshev_orthogonal (m n : ℕ) (h : m ≠ n) :
    ∫ x, Polynomial.eval x (monicChebyshev m) * Polynomial.eval x (monicChebyshev n)
      ∂Polynomial.Chebyshev.measureT = 0 := by
  have hbase := Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne h
  calc
    ∫ x, Polynomial.eval x (monicChebyshev m) * Polynomial.eval x (monicChebyshev n)
        ∂Polynomial.Chebyshev.measureT =
        ((Polynomial.Chebyshev.T ℝ m).leadingCoeff⁻¹ *
          (Polynomial.Chebyshev.T ℝ n).leadingCoeff⁻¹) *
          ∫ x, (Polynomial.Chebyshev.T ℝ m).eval x *
            (Polynomial.Chebyshev.T ℝ n).eval x ∂Polynomial.Chebyshev.measureT := by
      simp only [monicChebyshev, Polynomial.eval_mul, Polynomial.eval_C]
      rw [← MeasureTheory.integral_const_mul]
      congr with x
      ring
    _ = 0 := by rw [hbase, mul_zero]

theorem monicChebyshev_norm_ne_zero (n : ℕ) :
    ∫ x, (Polynomial.eval x (monicChebyshev n)) ^ 2
      ∂Polynomial.Chebyshev.measureT ≠ 0 := by
  have hc : (Polynomial.Chebyshev.T ℝ n).leadingCoeff⁻¹ ≠ 0 := by
    rw [Polynomial.Chebyshev.leadingCoeff_T]
    exact inv_ne_zero (pow_ne_zero _ (by norm_num))
  rw [show (∫ x, (Polynomial.eval x (monicChebyshev n)) ^ 2
      ∂Polynomial.Chebyshev.measureT) =
      (Polynomial.Chebyshev.T ℝ n).leadingCoeff⁻¹ ^ 2 *
        ∫ x, (Polynomial.Chebyshev.T ℝ n).eval x *
          (Polynomial.Chebyshev.T ℝ n).eval x ∂Polynomial.Chebyshev.measureT by
    rw [← MeasureTheory.integral_const_mul]
    congr with x
    simp [monicChebyshev, pow_two]
    ring]
  apply mul_ne_zero (pow_ne_zero _ hc)
  by_cases hn : n = 0
  · subst n
    have hzero :
        (∫ x, (Polynomial.Chebyshev.T ℝ (0 : ℕ)).eval x *
          (Polynomial.Chebyshev.T ℝ (0 : ℕ)).eval x
            ∂Polynomial.Chebyshev.measureT) = Real.pi := by
      simpa using Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero
    rw [hzero]
    exact Real.pi_ne_zero
  · rw [Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hn]
    exact div_ne_zero Real.pi_ne_zero (by norm_num)

end MetaMathlibExt
