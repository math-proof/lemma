import Mathlib
import Lemma.MvPolynomial.RothHelpers
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial


/--
[rothVanishesBelow_to_mv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {r : Fin m → ℕ}
  {c : RothCoeff r} {x : Fin m → ℝ} {T : ℝ}
-- given
  (hvan : rothVanishesBelow c x T) :
-- imply
  rothMvVanishesBelow
    (MvPolynomial.map (algebraMap ℤ ℝ) (rothMvOfCoeff c)) x r T := by
-- proof
  intro i hi
  rw [rothTranslate_coeff_eq_eval_hasse_h, ← rothMvHasse_map_h,
    ← MvPolynomial.eval₂_eq_eval_map, rothMvHasse_eval_ofCoeff_index_h]
  apply hvan (fun h ↦ i h)
  simpa [rothWeight, rothMvWeight] using hi


-- created on 2026-10-21
