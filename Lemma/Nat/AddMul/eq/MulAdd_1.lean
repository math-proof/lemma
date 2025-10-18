import Lemma.Nat.MulAdd.eq.AddMulS
open Nat


@[main, comm]
private lemma main
  [Semiring α]
  {k d : α} :
-- imply
  k * d + d = (k + 1) * d := by
-- proof
  simp [MulAdd.eq.AddMulS]


-- created on 2025-03-30
