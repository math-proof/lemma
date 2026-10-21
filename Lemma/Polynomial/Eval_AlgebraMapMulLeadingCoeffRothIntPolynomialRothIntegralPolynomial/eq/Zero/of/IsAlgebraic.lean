import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.Eval_MapRothIntPolynomialAlgebraMap.eq.Zero
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial
open scoped nonZeroDivisors


/--
[rothIntegralPolynomial_isRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  eval₂ (algebraMap ℤ ℝ)
    (((rothIntPolynomial α).leadingCoeff : ℝ) * α)
    (rothIntegralPolynomial α) = 0 := by
-- proof
  have hfne : rothIntPolynomial α ≠ 0 := by
    obtain ⟨b, hb, hspec⟩ :=
      IsLocalization.integerNormalization_spec ℤ⁰ (minpoly ℚ α)
    intro hzero
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have hbQ : algebraMap ℤ ℚ b ≠ 0 := Int.cast_ne_zero.mpr hb0
    have heq : b • minpoly ℚ α = 0 := by
      rw [← hspec]
      simpa [rothIntPolynomial] using congrArg (map (algebraMap ℤ ℚ)) hzero
    refine absurd heq ?_
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
    exact mul_ne_zero (C_ne_zero.mpr hbQ) (minpoly.ne_zero hα.isIntegral)
  let f := rothIntPolynomial α
  have hf : f ≠ 0 := hfne
  have hd0 : f.natDegree ≠ 0 := by
    intro hd
    have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hd
    have hr := Eval_MapRothIntPolynomialAlgebraMap.eq.Zero α
    change eval α (f.map (algebraMap ℤ ℝ)) = 0 at hr
    rw [hfC, map_C, eval_C] at hr
    have hc : f.coeff 0 = 0 := Int.cast_eq_zero.mp hr
    apply hf
    rw [hfC, hc, C_0]
  have hd : 1 ≤ f.natDegree := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd0)
  have hfroot : eval₂ (algebraMap ℤ ℝ) α f = 0 := by
    simpa [f, eval_map] using Eval_MapRothIntPolynomialAlgebraMap.eq.Zero α
  change eval₂ (algebraMap ℤ ℝ) ((f.leadingCoeff : ℝ) * α)
    f.integralNormalization = 0
  calc
    _ = (algebraMap ℤ ℝ f.leadingCoeff) ^ (f.natDegree - 1) *
        eval₂ (algebraMap ℤ ℝ) α f := by
      simpa using
        integralNormalization_eval₂_leadingCoeff_mul hd
          (algebraMap ℤ ℝ) α
    _ = 0 := by
      rw [hfroot, mul_zero]


-- created on 2026-10-21
