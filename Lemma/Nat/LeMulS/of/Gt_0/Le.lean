import Lemma.Nat.Ge.of.Gt
import Lemma.Algebra.LeMulS.of.Ge_0.Le
open Algebra Nat


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h₀ : x > 0)
  (h₁ : a ≤ b) :
-- imply
  x * a ≤ x * b := by
-- proof
  have h := Ge.of.Gt h₀
  apply LeMulS.of.Ge_0.Le h h₁


-- created on 2024-07-01
-- updated on 2025-04-06
