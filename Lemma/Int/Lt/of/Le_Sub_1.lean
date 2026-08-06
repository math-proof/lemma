import Lemma.Int.Le_Sub.is.LeAdd
import Lemma.Nat.Lt.of.Lt.Le
open Int Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Lt.of.Le_Sub_1 |
| comm 1 | Int.Gt.of.GeSub_1 |
-/
@[main, comm 1]
private lemma main
  [Ring α]
  [LinearOrder α]
  [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : x ≤ y - 1) :
-- imply
  x < y :=
-- proof
  Lt.of.Lt.Le (lt_add_one x) (LeAdd.of.Le_Sub h)


-- created on 2018-05-23
-- updated on 2025-05-07
