import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path, comm, mp, mpr]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n is even ↔ n % 2 = 0 :=
-- proof
  IntegerRing.even_iff


-- created on 2025-03-05
-- updated on 2026-10-26
