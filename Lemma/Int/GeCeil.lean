import Lemma.Set.In_IocCeil
open Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.GeCeil |
| comm | Int.Le_Ceil |
-/
@[main, comm]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌈x⌉ ≥ x := by
-- proof
  have := In_IocCeil (x := x)
  exact this.right


-- created on 2018-05-10
-- updated on 2026-08-22
