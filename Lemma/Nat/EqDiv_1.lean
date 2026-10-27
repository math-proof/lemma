import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n / 1 = n :=
-- proof
  IntegerRing.div_one n


-- created on 2025-07-11
-- updated on 2026-10-26
