import Lemma.Nat.Le.of.Lt
import Lemma.Int.LeMulS.of.Ge_0.Le
open Nat Int


/--
This lemma asserts that in a preordered algebraic structure with monotonic multiplication by non-negative elements, multiplying both sides of a strict inequality by a non-negative element preserves the inequality.
Specifically, if `x ≥ 0` and `a < b`, then `x * a ≤ x * b`.
-/
@[main]
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
