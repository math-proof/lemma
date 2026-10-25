/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Recurrences/GolombLikeSequence.lean -/


import Mathlib.Tactic
import Theorem.NumberTheory.Recurrences.GolombLikeSequence.Part8
import Lemma.Nat.Recurrences.GolombLikeSequence


namespace MetaMathlibExt

-- The case `f (f n) = 2n + 1` has the asserted unique increasing solution.
example :
    ∃! f : ℕ+ → ℕ+,
      StrictMono f ∧
      (↑((f 1).val) : ℚ) = 2 ∧
      ∀ n : ℕ+, (↑((f (f n)).val) : ℤ) = 2 * (↑n.val : ℤ) + 1 := by
  have h := (golomb_like_closed_form 2 1 (by norm_num) (by norm_num) (by norm_num)).1
  norm_num at h ⊢
  exact h

-- The zero offset in the first block gives `m = 2` and `f m = 3`.
example (f : ℕ+ → ℕ+) (hf : StrictMono f)
    (hone : (↑((f 1).val) : ℚ) = 2)
    (hcomp : ∀ n : ℕ+, (↑((f (f n)).val) : ℤ) = 2 * (↑n.val : ℤ) + 1) :
    ∃ m : ℕ+, (↑m.val : ℚ) = 2 ∧ (↑((f m).val) : ℚ) = 3 := by
  have h := (golomb_like_closed_form 2 1 (by norm_num) (by norm_num) (by norm_num)).2
    f hf (by norm_num at hone ⊢; exact hone) hcomp 0 0 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end MetaMathlibExt
