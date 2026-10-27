import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [IntegerRing Z]
  {a : Z}
-- given
  (h : a ≠ 0) :
-- imply
  a / a = 1 :=
-- proof
  IntegerRing.div_self h


-- created on 2026-01-10
