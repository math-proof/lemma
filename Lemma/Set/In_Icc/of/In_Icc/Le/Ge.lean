import Lemma.Algebra.Lt.of.Lt.Ge
import Lemma.Set.In_Icc.is.Le.Le
open Algebra Set


@[main]
private lemma main
  [Preorder α]
  {a b a' b' x : α}
-- given
  (h₀ : a' ≤ a)
  (h₁ : b' ≥ b)
  (h : x ∈ Icc a b) :
-- imply
  x ∈ Icc a' b' := by
-- proof
  apply In_Icc.of.Le.Le
  ·
    exact le_trans h₀ (Le.Le.of.In_Icc h).1
  ·
    exact le_trans (Le.Le.of.In_Icc h).2 h₁


-- created on 2026-08-20
