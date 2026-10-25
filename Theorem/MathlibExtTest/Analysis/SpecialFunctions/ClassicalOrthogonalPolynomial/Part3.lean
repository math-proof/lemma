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
import Def.MathlibExtTest.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial.Part2


namespace MetaMathlibExt

open MeasureTheory Set Real

open scoped NNReal

theorem chebyshevWeight_nonneg (x : ℝ) : 0 ≤ chebyshevWeight x := by
  change 0 ≤ (Real.sqrt (1 - x ^ 2))⁻¹
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem integral_chebyshevMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂chebyshevMeasure = ∫ x, f x ∂Polynomial.Chebyshev.measureT := by
  rw [Polynomial.Chebyshev.integral_measureT]
  unfold chebyshevMeasure
  rw [intervalIntegral.integral_of_le (by norm_num)]
  let wnn : ℝ → ℝ≥0 := fun x =>
    ⟨Real.sqrt (1 - x ^ 2)⁻¹, by positivity⟩
  have hdensity : (fun x => ENNReal.ofReal (chebyshevWeight x)) =
      (fun x => (wnn x : ENNReal)) := by
    funext x
    simp only [chebyshevWeight, Pi.inv_apply, wnn, Real.sqrt_inv]
    exact ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr (Real.sqrt_nonneg _))
  rw [hdensity]
  rw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr! 2 with x
  rw [NNReal.smul_def]
  change Real.sqrt (1 - x ^ 2)⁻¹ * f x = f x * Real.sqrt (1 - x ^ 2)⁻¹
  exact mul_comm _ _

theorem monicChebyshev_orthogonal_explicit (m n : ℕ) (h : m ≠ n) :
    ∫ x, Polynomial.eval x (monicChebyshev m) * Polynomial.eval x (monicChebyshev n)
      ∂chebyshevMeasure = 0 := by
  rw [integral_chebyshevMeasure]
  exact monicChebyshev_orthogonal m n h

theorem monicChebyshev_norm_ne_zero_explicit (n : ℕ) :
    ∫ x, (Polynomial.eval x (monicChebyshev n)) ^ 2 ∂chebyshevMeasure ≠ 0 := by
  rw [integral_chebyshevMeasure]
  exact monicChebyshev_norm_ne_zero n

theorem chebyshevWeight_classical : ∃ u0 u1 v0 v1 v2 : ℝ,
    (v0 ≠ 0 ∨ v1 ≠ 0 ∨ v2 ≠ 0) ∧
      ∀ x : ℝ, x ∈ interior (Set.Ioc (-1) 1) →
        DifferentiableAt ℝ chebyshevWeight x ∧
          (v0 + v1 * x + v2 * x ^ 2) * deriv chebyshevWeight x =
            (u0 + u1 * x) * chebyshevWeight x := by
  refine ⟨0, 1, 1, 0, -1, by norm_num, ?_⟩
  intro x hx
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa using hx
  have hs : 0 < 1 - x ^ 2 := by
    rcases hx' with ⟨hxlo, hxhi⟩
    nlinarith
  have hquad : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat, neg_mul] using
      (hasDerivAt_pow 2 x).const_sub 1
  have hsqrt := hquad.sqrt (ne_of_gt hs)
  have hsqrt_ne : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hs
  have hinv := hsqrt.inv hsqrt_ne
  have hdiff : DifferentiableAt ℝ chebyshevWeight x := by
    simpa only [chebyshevWeight] using hinv.differentiableAt
  have hderiv : deriv chebyshevWeight x =
      -(-2 * x / (2 * Real.sqrt (1 - x ^ 2))) /
        (Real.sqrt (1 - x ^ 2)) ^ 2 := by
    simpa only [chebyshevWeight] using hinv.deriv
  refine ⟨hdiff, ?_⟩
  rw [hderiv]
  simp only [zero_add, one_mul, zero_mul, add_zero, neg_one_mul, chebyshevWeight,
    Pi.inv_apply]
  field_simp
  rw [Real.sq_sqrt hs.le]
  ring

end MetaMathlibExt
