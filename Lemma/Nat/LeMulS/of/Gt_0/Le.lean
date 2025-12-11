import Lemma.Int.LeMulS.of.Ge_0.Le
import Lemma.Nat.Ge.of.Gt
open Int Nat


@[main, comm 1]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h₀ : x > 0)
  (h₁ : a ≤ b) :
-- imply
  x * a ≤ x * b := by
-- proof
  apply LeMulS.of.Ge_0.Le _ h₁
  apply Ge.of.Gt h₀


-- created on 2025-12-11
