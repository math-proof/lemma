import Lemma.Nat.LeMulS.of.Le.Gt_0
import Lemma.Nat.Lt.of.Le.Lt
import Lemma.Nat.LtMulS.of.Gt_0.Lt
open Nat


@[main, comm 12]
private lemma main
  [Mul α] [Zero α] [Preorder α]
  [PosMulStrictMono α] [MulPosMono α]
  {x a b : α}
-- given
  (h_b : b > 0)
  (h_x : x > 0)
  (h₁ : a ≤ b)
  (h₂ : x < y) :
-- imply
  a * x < b * y := by
-- proof
  have := LtMulS.of.Gt_0.Lt h_b h₂
  apply Lt.of.Le.Lt _ this
  apply LeMulS.of.Le.Gt_0 h₁ h_x


-- created on 2026-07-19
