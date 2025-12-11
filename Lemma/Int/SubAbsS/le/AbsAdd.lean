import Lemma.Int.SubAbsS.le.AbsSub
open Int


@[main]
private lemma main
  [AddCommGroup G]
  [LinearOrder G]
  [IsOrderedAddMonoid G]
-- given
  (a b : G) :
-- imply
  |a| - |b| ≤ |a + b| := by
-- proof
  have := SubAbsS.le.AbsSub a (-b)
  simp at this
  simpa


-- created on 2025-12-11
