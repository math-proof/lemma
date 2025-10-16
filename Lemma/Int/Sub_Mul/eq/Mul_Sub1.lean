import Lemma.Int.Mul_Sub.eq.SubMulS
open Int


@[main]
private lemma main
  [Ring α]
  {x b : α} :
-- imply
  x - x * b = x * (1 - b) := by
-- proof
  rw [Mul_Sub.eq.SubMulS]
  simp


-- created on 2025-04-20
-- updated on 2025-10-16
