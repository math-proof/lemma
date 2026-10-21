import Mathlib
import Lemma.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial


/--
[roth_rational_vanishing_of_real_hasse_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ) (q : Fin m → ℚ) (r : Fin m → ℕ) (θ : ℝ)
-- given
  (hzero : ∀ i : RothMvIndex m, rothMvWeight r i ≤ θ →
    MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ))
      (rothMvHasse i P) = 0) :
-- imply
  rothMvVanishesBelow (MvPolynomial.map (algebraMap ℤ ℚ) P) q r θ := by
-- proof
  intro i hi
  rw [rothTranslate_coeff_eq_eval_hasse_h, ← rothMvHasse_map_h,
    ← MvPolynomial.eval₂_eq_eval_map]
  have hcast := roth_eval₂_rat_cast_h (rothMvHasse i P) q
  rw [hzero i hi.le] at hcast
  norm_num at hcast
  exact_mod_cast hcast


-- created on 2026-10-21
