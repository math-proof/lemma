import Lemma.Int.LtAbsSub.is.LtSub.Lt_Add
open Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LtAbs.is.LtNeg.Lt |
| comm | Int.LtNeg.Lt.is.LtAbs |
| mp | Int.LtNeg.Lt.of.LtAbs |
| mpr | Int.LtAbs.of.LtNeg.Lt |
| mp.left | Int.LtNeg.of.LtAbs |
| mp.right | Int.Lt.of.LtAbs |
-/
@[main, comm, mp, mpr, mp.left, mp.right]
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
