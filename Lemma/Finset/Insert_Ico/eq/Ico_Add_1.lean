import sympy.Basic
import sympy.sets.sets


@[main]
private lemma main
  [Preorder α] [LocallyFiniteOrder α]
-- given
  (a n : α) :
-- imply
  insert (a + n) (Finset.Ico a (a + n)) = Finset.Ico a (a + n + 1) := by
-- proof
  have h : a ≤ a + n := by omega
  simpa [Nat.cast_add, add_assoc] using Finset.insert_Ico_right_eq_Ico_add_one (a := a) (b := a + n) h


-- created on 2026-08-05
