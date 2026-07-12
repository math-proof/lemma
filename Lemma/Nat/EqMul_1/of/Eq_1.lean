import Lemma.Nat.EqMul_1
open Nat


@[main]
private lemma main
  [MulOneClass M]
  {a : M}
  -- given
  (h : n = 1) :
-- imply
  a * n = a :=
-- proof
  h.symm.subst (motive := fun n => a * n = a) (EqMul_1 a)


-- created on 2025-10-26
