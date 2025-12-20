import Lemma.Nat.LeMulS.of.Gt_0.Le
import Lemma.Nat.Lt.of.Lt.Le
import Lemma.Nat.LtMulS.of.Lt.Gt_0
open Nat


@[main, comm 12]
private lemma main
  [Mul α] [Zero α] [Preorder α]
  [MulPosStrictMono α] [PosMulMono α]
  {x a b : α}
-- given
  (h_b : b > 0)
  (h_x : x > 0)
  (h₁ : a < b)
  (h₂ : x ≤ y) :
-- imply
  a * x < b * y := by
-- proof
  have := LtMulS.of.Lt.Gt_0 h₁ h_x
  apply Lt.of.Lt.Le this
  apply LeMulS.of.Gt_0.Le h_b h₂


-- created on 2025-12-20
