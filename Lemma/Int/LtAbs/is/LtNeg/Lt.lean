import Lemma.Int.LtAbsSub.is.LtSub.Lt_Add
open Int


@[main, comm, mp, mpr]
private lemma main
  [AddCommGroup α]
  [LinearOrder α]
  [IsOrderedAddMonoid α]
-- given
  (x d : α) :
-- imply
  |x| < d ↔ -d < x ∧ x < d := by
-- proof
  have := LtAbsSub.is.LtSub.Lt_Add x 0 d
  simp at this
  grind


-- created on 2025-12-09
