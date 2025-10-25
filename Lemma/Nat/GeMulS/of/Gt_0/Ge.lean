import Lemma.Int.LeMulS.of.Ge_0.Le
import Lemma.Nat.Ge.of.Gt
open Nat Int


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h₀ : x > 0)
  (h₁ : a ≥ b) :
-- imply
  x * a ≥ x * b := by
-- proof
  have h := Ge.of.Gt h₀
  apply LeMulS.of.Ge_0.Le h h₁


-- created on 2024-07-01
