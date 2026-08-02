import Lemma.Int.Mul_Sub.eq.SubMulS
open Int


@[main, comm]
private lemma main
  [Ring α]
  {x a : α} :
-- imply
  x * a - x = x * (a - 1) := by
-- proof
  simp [Mul_Sub.eq.SubMulS]


-- created on 2026-08-02
