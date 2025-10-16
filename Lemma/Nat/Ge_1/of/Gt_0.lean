import Lemma.Nat.Ge_Add_1.of.Gt
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {x : Z}
-- given
  (h : x > 0) :
-- imply
  x ≥ 1 := by
-- proof
  have := Ge_Add_1.of.Gt h
  simp at this
  assumption


-- created on 2025-05-24
