import Lemma.Nat.EqMul_1
open Nat


@[main]
private lemma main
  [MulOneClass M]
  {a : M}
  -- given
  (h : n = 1) :
-- imply
  a * n = a := by
-- proof
  subst h
  apply EqMul_1


-- created on 2025-10-26
