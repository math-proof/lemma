import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n < n + 1 :=
-- proof
  IntegerRing.lt_succ_self n


-- created on 2025-08-13
