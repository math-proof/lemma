import Lemma.Algebra.Gt.is.Ge.Ne
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  a ≠ b ∧ a ≥ b ↔ a > b := by
-- proof
  rw [And.comm]
  apply Ge.Ne.is.Gt


-- created on 2025-04-18
