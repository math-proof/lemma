import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open scoped nonZeroDivisors Polynomial


/--
[rothIntPolynomial_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {α : ℝ}
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  rothIntPolynomial α ≠ 0 := by
-- proof
  obtain ⟨b, hb, hspec⟩ :=
    IsLocalization.integerNormalization_spec ℤ⁰ (minpoly ℚ α)
  intro hf
  change IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ α) = 0 at hf
  apply mul_ne_zero
    (Polynomial.C_ne_zero.mpr
      (Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hb)))
    (minpoly.ne_zero hα.isIntegral)
  convert_to b • minpoly ℚ α = 0
  ·
    rw [Algebra.smul_def]
    rfl
  rw [← hspec, hf, Polynomial.map_zero]


-- created on 2026-10-21
