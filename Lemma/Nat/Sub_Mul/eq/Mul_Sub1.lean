import Lemma.Nat.Mul_Sub.eq.SubMulS
import Lemma.Int.Mul_Sub.eq.SubMulS
open Nat Int


@[path]
private lemma main
  {x b : ℕ} :
-- imply
  x - x * b = x * (1 - b) := by
-- proof
  rw [Mul_Sub.eq.SubMulS]
  simp


-- created on 2025-10-16
