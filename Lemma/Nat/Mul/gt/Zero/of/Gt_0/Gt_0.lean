import Lemma.Nat.GtMulS.of.Gt_0.Gt
import Lemma.Nat.EqMul_0'0
open Nat


@[main]
private lemma main
  [MulZeroClass α] [Preorder α] [PosMulStrictMono α]
  {a b : α}
-- given
  (h₀ : a > 0)
  (h₁ : b > 0) :
-- imply
  a * b > 0 := by
-- proof
  have h := GtMulS.of.Gt_0.Gt h₀ h₁
  simp only [EqMul_0'0] at h
  exact h


-- created on 2024-11-25
