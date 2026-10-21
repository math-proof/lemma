import Mathlib
import Lemma.Fin.RothRidoutComplement.eq.Sub.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_ridout_weight_complement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (r : Fin m → ℕ) (i : RothMvIndex m)
-- given
  (hr : ∀ h, 0 < r h)
  (hi : ∀ h, i h ≤ r h) :
-- imply
  rothMvWeight r (rothRidoutComplement r i) = m - rothMvWeight r i :=
-- proof
  calc
    _ = ∑ h, (1 - (i h : ℝ) / r h) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [RothRidoutComplement.eq.Sub.of.RothMvIndex, Nat.cast_sub (hi h)]
      have hr0 : (r h : ℝ) ≠ 0 := by exact_mod_cast (hr h).ne'
      field_simp
    _ = (m : ℝ) - rothMvWeight r i := by
      rw [Finset.sum_sub_distrib]
      simp [rothMvWeight]


-- created on 2026-10-21
