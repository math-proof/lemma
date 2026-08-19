import Lemma.Set.In_IocCeil
open Set


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (x : α) :
-- imply
  x > ⌈x⌉ - 1 := by
-- proof
  have := In_IocCeil (x := x)
  exact this.left


-- created on 2018-10-28
