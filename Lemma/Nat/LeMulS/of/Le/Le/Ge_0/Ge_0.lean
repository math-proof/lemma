import Lemma.Int.LeMulS.of.Ge_0.Le
import Lemma.Int.LeMulS.of.Le.Ge_0
import Lemma.Nat.Le.of.Le.Le
open Int Nat


@[main, comm 12]
private lemma main
  [Mul α] [Zero α] [Preorder α]
  [MulPosMono α] [PosMulMono α]
  {x a b : α}
-- given
  (h_b : b ≥ 0)
  (h_x : x ≥ 0)
  (h₁ : a ≤ b)
  (h₂ : x ≤ y) :
-- imply
  a * x ≤ b * y := by
-- proof
  have := LeMulS.of.Le.Ge_0 h₁ h_x
  apply Le.of.Le.Le this
  apply LeMulS.of.Ge_0.Le h_b h₂


-- created on 2025-12-17
