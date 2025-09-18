import Lemma.Algebra.MulSub.eq.SubMulS
open Algebra


@[main, comm]
private lemma nat
  {x a : ℕ} :
-- imply
  a * x - x = (a - 1) * x := by
-- proof
  simp [MulSub.eq.SubMulS.nat]


@[main, comm]
private lemma main
  [Ring α]
  {x a : α} :
-- imply
  a * x - x = (a - 1) * x := by
-- proof
  simp [MulSub.eq.SubMulS]


-- created on 2025-03-31
