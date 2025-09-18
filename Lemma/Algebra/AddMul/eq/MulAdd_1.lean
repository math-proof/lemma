import Lemma.Algebra.MulAdd.eq.AddMulS
open Algebra


@[main, comm]
private lemma main
  [Semiring α]
  {k d : α} :
-- imply
  k * d + d = (k + 1) * d := by
-- proof
  simp [MulAdd.eq.AddMulS]


-- created on 2025-03-30
