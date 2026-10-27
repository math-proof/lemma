import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path, comm 1]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x + 1 ≤ y) :
-- imply
  x < y :=
-- proof
  IntegerRing.lt_of_succ_le h


-- created on 2025-03-30
