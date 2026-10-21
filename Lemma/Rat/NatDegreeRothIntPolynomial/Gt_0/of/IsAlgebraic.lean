import Mathlib
import Lemma.Rat.RothIntPolynomial.ne.Zero.of.IsAlgebraic
open MathlibExt.NumberTheory.RothAuxiliary
open Rat
open scoped nonZeroDivisors Polynomial


private lemma rothIntPolynomial_isRoot
  (α : ℝ) :
  Polynomial.eval α ((rothIntPolynomial α).map (algebraMap ℤ ℝ)) = 0 := by
  obtain ⟨b, _, hspec⟩ :=
    IsLocalization.integerNormalization_spec ℤ⁰ (minpoly ℚ α)
  change Polynomial.eval α
    ((IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ α)).map
      (algebraMap ℤ ℝ)) = 0
  have hmap : algebraMap ℤ ℝ = (algebraMap ℚ ℝ).comp (algebraMap ℤ ℚ) := by
    ext
    simp
  have hmapsmul :
    Polynomial.map (algebraMap ℚ ℝ) (b • minpoly ℚ α) =
      b • Polynomial.map (algebraMap ℚ ℝ) (minpoly ℚ α) :=
    map_zsmul (Polynomial.mapRingHom (algebraMap ℚ ℝ)) b (minpoly ℚ α)
  have hroot : Polynomial.eval₂ (algebraMap ℚ ℝ) α (minpoly ℚ α) = 0 := by
    rw [← Polynomial.aeval_def]
    apply minpoly.aeval
  rw [hmap, ← Polynomial.map_map, hspec, hmapsmul, Polynomial.eval_smul]
  simp [Polynomial.eval_map, hroot]

/--
[rothIntPolynomial_natDegree_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {α : ℝ}
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  0 < (rothIntPolynomial α).natDegree := by
-- proof
  let f := rothIntPolynomial α
  by_contra hnot
  have hfC : f = Polynomial.C (f.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hnot)
  have hr := rothIntPolynomial_isRoot α
  change Polynomial.eval α (f.map (algebraMap ℤ ℝ)) = 0 at hr
  rw [hfC, Polynomial.map_C, Polynomial.eval_C] at hr
  apply RothIntPolynomial.ne.Zero.of.IsAlgebraic hα
  change f = 0
  rw [hfC, Int.cast_eq_zero.mp hr, Polynomial.C_0]


-- created on 2026-10-21
