import Lemma.Algebra.Lt.of.Lt.Le
import Lemma.Algebra.Le.of.Lt
open Algebra


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a < b)
  (h₁ : b ≤ c) :
-- imply
  a ≤ c := by
-- proof
  have := Lt.of.Lt.Le h₀ h₁
  apply Le.of.Lt this


-- created on 2025-06-20
