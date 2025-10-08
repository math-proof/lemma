import Lemma.Algebra.Lt.of.Lt.Lt
import Lemma.Nat.Le.of.Lt
open Algebra Nat


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a < b)
  (h₁ : b < c) :
-- imply
  a ≤ c := by
-- proof
  apply Le.of.Lt
  apply Lt.of.Lt.Lt h₀ h₁


-- created on 2025-05-18
