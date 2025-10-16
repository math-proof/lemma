import sympy.sets.sets
import Lemma.Algebra.GeAddS.is.Ge
import Lemma.Nat.LtAddS.is.Lt
open Algebra Nat


@[main]
private lemma main
  [Preorder α]
  [Add α]
  [AddLeftMono α]
  [AddRightMono α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {x a b : α}
-- given
  (h : x ∈ Ico a b)
  (t : α) :
-- imply
  x + t ∈ Ico (a + t) (b + t) := by
-- proof
  let ⟨h₀, h₁⟩ := h
  have h₀ := GeAddS.of.Ge t h₀
  have h₁ := LtAddS.of.Lt t h₁
  exact ⟨h₀, h₁⟩


-- created on 2025-08-02
