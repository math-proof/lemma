import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path, comm]
private lemma main
  [IntegerRing Z]
  {b c : Z}
-- given
  (h : c ∣ b)
  (a : Z) :
-- imply
  a * b / c = a * (b / c) :=
-- proof
  IntegerRing.mul_div_assoc a h


-- created on 2025-07-08
