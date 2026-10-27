import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [IntegerRing N]
  {a b : N}
-- given
  (h : b ≥ a) :
-- imply
  b - a + a = b :=
-- proof
  IntegerRing.sub_add_cancel h


-- created on 2025-03-15
-- updated on 2026-10-26
