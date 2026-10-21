import Mathlib
import Lemma.Fin.GetRothRidoutBoxComplement.eq.Sub.of.RothBox
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_ridout_weight_box_complement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (r : Fin m → ℕ)
-- given
  (hr : ∀ h, 0 < r h)
  (j : RothBox r) :
-- imply
  rothWeight r (fun h ↦ rothRidoutBoxComplement r j h) =
    (m : ℝ) - rothWeight r (fun h ↦ j h) :=
-- proof
  calc
    _ = ∑ h, (1 - (j h : ℝ) / r h) := by
      unfold rothWeight
      apply Finset.sum_congr rfl
      intro h _
      change (((rothRidoutBoxComplement r j) h : ℕ) : ℝ) / r h =
        1 - (j h : ℝ) / r h
      rw [GetRothRidoutBoxComplement.eq.Sub.of.RothBox,
        Nat.cast_sub (Nat.le_of_lt_succ (j h).isLt)]
      have hr0 : (r h : ℝ) ≠ 0 := by exact_mod_cast (hr h).ne'
      field_simp
    _ = (m : ℝ) - rothWeight r (fun h ↦ j h) := by
      rw [Finset.sum_sub_distrib]
      simp [rothWeight]


-- created on 2026-10-21
