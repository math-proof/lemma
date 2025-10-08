import Lemma.Nat.Le.of.Lt
open Nat


/--
**Lemma:** If `x` is strictly greater than `y` in a preorder, then `x` is greater than or equal to `y`.
This lemma establishes that a strict inequality (`x > y`) implies the corresponding non-strict inequality (`x ≥ y`) within the context of a preorder.
It leverages the foundational property `Le.of.Lt` to convert between strict and non-strict inequalities, which is essential in ordered algebraic structures.
-/
@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≥ y := by
-- proof
  exact Le.of.Lt h


-- created on 2024-07-01
-- updated on 2025-04-04
