import sympy.sets.sets
import Lemma.Algebra.LtAddS.of.Lt.Lt
open Algebra


@[main]
private lemma main
  [Preorder α]
  [Add α]
  [AddRightStrictMono α]
  [AddLeftStrictMono α]
  {a b c d x₀ x₁ : α}
-- given
  (h₀ : x₀ ∈ Ioo a b)
  (h₁ : x₁ ∈ Ioo c d) :
-- imply
  x₀ + x₁ ∈ Ioo (a + c) (b + d) := by
-- proof
  let ⟨h₀_gt, h₀_lt⟩ := h₀
  let ⟨h₁_gt, h₁_lt⟩ := h₁
  have h_gt := LtAddS.of.Lt.Lt h₀_gt h₁_gt
  have h_le := LtAddS.of.Lt.Lt h₀_lt h₁_lt
  simp_all


-- created on 2025-09-29
