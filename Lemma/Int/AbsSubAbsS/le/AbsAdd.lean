import Lemma.Int.AbsSubAbsS.le.AbsSub
open Int


@[main]
private lemma main
  [AddCommGroup G]
  [LinearOrder G]
  [IsOrderedAddMonoid G]
-- given
  (a b : G) :
-- imply
  |(|a| - |b|)| ≤ |a + b| := by
-- proof
  have := AbsSubAbsS.le.AbsSub a (-b)
  simp at this
  assumption


-- created on 2025-12-11
