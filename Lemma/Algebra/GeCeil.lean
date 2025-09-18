import Lemma.Set.In_IocCeil
open Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌈x⌉ ≥ x := by
-- proof
  have := In_IocCeil (x := x)
  exact this.right


-- created on 2025-05-04
