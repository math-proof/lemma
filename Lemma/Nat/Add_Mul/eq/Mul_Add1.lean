import Lemma.Nat.Mul_Add.eq.AddMulS
open Nat


@[main, comm]
private lemma main
  [Semiring α]
  {k d : α} :
-- imply
  d + d * k = d * (1 + k) := by
-- proof
  simp [Mul_Add.eq.AddMulS]


-- created on 2025-05-04
