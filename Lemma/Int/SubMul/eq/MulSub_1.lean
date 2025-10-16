import Lemma.Int.MulSub.eq.SubMulS
open Int


@[main, comm]
private lemma main
  [Ring α]
  {x a : α} :
-- imply
  a * x - x = (a - 1) * x := by
-- proof
  simp [MulSub.eq.SubMulS]


-- created on 2025-10-16
