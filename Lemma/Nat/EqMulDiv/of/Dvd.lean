import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [IntegerRing Z]
  {a b : Z}
-- given
  (h : b ∣ a) :
-- imply
  a / b * b = a :=
-- proof
  IntegerRing.div_mul_cancel h


-- created on 2025-07-08
