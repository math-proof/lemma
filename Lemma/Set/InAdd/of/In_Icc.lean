import sympy.sets.sets
import Lemma.Nat.LeAddS.is.Le
open Nat


@[main]
private lemma main
  [Preorder α]
  [Add α]
  [AddLeftMono α]
  [AddRightMono α]
  {x a b : α}
-- given
  (h : x ∈ Icc a b)
  (t : α) :
-- imply
  x + t ∈ Icc (a + t) (b + t) := by
-- proof
  let ⟨h₀, h₁⟩ := h
  have h₀ := GeAddS.of.Ge t h₀
  have h₁ := LeAddS.of.Le t h₁
  exact ⟨h₀, h₁⟩


-- created on 2026-10-02
