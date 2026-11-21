import Theorem.Nat.EqMulDiv.of.Dvd
import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic
open Nat


@[path]
private lemma main
  [IntegerRing Z]
  {n : Z} :
-- imply
  n / n * n = n := by
-- proof
  apply EqMulDiv.of.Dvd
  simp


-- created on 2026-01-10
-- updated on 2026-11-21
