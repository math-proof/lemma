import sympy.sets.sets
import Lemma.Nat.Lt.of.Lt.Le
import Lemma.Set.In_Icc.is.Le.Le
open Nat Set


@[main]
private lemma main
  [Preorder α]
  {a b a' b' x : α}
-- given
  (h₀ : a' ≤ a)
  (h₁ : b' ≥ b)
  (h : x ∈ Ico a b) :
-- imply
  x ∈ Ico a' b' :=
-- proof
  ⟨le_trans h₀ h.1, Lt.of.Lt.Le h.2 h₁⟩


-- created on 2018-11-05
-- updated on 2026-08-20
