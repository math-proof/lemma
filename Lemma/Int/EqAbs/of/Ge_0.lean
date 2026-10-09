import Lemma.Int.Abs.eq.IteGe_0


@[path]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : 0 ≤ x) :
-- imply
  |x| = x := by
-- proof
  exact abs_of_nonneg h


-- created on 2026-10-03
