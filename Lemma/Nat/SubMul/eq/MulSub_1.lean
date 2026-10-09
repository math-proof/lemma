import Lemma.Nat.MulSub.eq.SubMulS
import Lemma.Int.MulSub.eq.SubMulS
open Nat Int


@[path, comm]
private lemma main
  {x a : ℕ} :
-- imply
  a * x - x = (a - 1) * x := by
-- proof
  simp [MulSub.eq.SubMulS]


-- created on 2025-03-31
-- updated on 2025-10-16
