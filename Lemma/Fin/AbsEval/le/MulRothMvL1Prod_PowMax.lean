import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_abs_eval₂_le_l1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {P : MvPolynomial (Fin m) ℤ}
  {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBound P r)
  (x : Fin m → ℝ) :
-- imply
  |MvPolynomial.eval₂ (algebraMap ℤ ℝ) x P| ≤
    (rothMvL1 P : ℝ) * ∏ h, max 1 |x h| ^ r h := by
-- proof
  classical
  rw [MvPolynomial.eval₂_eq']
  calc
    _ ≤ ∑ d ∈ P.support,
          |(algebraMap ℤ ℝ) (P.coeff d) * ∏ h, x h ^ d h| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.support,
          ((P.coeff d).natAbs : ℝ) * ∏ h, max 1 |x h| ^ r h := by
      gcongr with d hd
      rw [abs_mul, Finset.abs_prod]
      have hcoeff : |(algebraMap ℤ ℝ) (P.coeff d)| = ((P.coeff d).natAbs : ℝ) := by
        rw [algebraMap_int_eq, Int.coe_castRingHom]
        norm_num
      rw [hcoeff]
      gcongr with h
      rw [abs_pow]
      apply (pow_le_pow_left₀ (abs_nonneg _) (le_max_right 1 |x h|) _).trans
      apply pow_le_pow_right₀ (le_max_left _ _) (hP d hd h)
    _ = (rothMvL1 P : ℝ) * ∏ h, max 1 |x h| ^ r h := by
      rw [← Finset.sum_mul]
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support]
      norm_cast


-- created on 2026-10-21
