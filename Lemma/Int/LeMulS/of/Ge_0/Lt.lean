import Lemma.Nat.Le.of.Lt
import Lemma.Int.LeMulS.of.Ge_0.Le
open Nat Int


@[main, comm 1]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : a < b) :
-- imply
  x * a ≤ x * b := by
-- proof
  have h := Le.of.Lt h₁
  apply LeMulS.of.Ge_0.Le h₀ h


-- created on 2024-07-01
-- updated on 2025-04-04
