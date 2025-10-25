import sympy.sets.sets
import Lemma.Nat.LeAddS.of.Le.Le
import Lemma.Nat.LtAddS.of.Lt.Lt
open Nat


@[main]
private lemma main
  [Preorder α]
  [Add α]
  [AddRightMono α]
  [AddLeftMono α]
  [AddRightStrictMono α]
  [AddLeftStrictMono α]
  {a b c d x₀ x₁ : α}
-- given
  (h₀ : x₀ ∈ Ico a b)
  (h₁ : x₁ ∈ Ico c d) :
-- imply
  x₀ + x₁ ∈ Ico (a + c) (b + d) := by
-- proof
  let ⟨h₀_ge, h₀_lt⟩ := h₀
  let ⟨h₁_ge, h₁_lt⟩ := h₁
  have h_gt := LeAddS.of.Le.Le h₀_ge h₁_ge
  have h_le := LtAddS.of.Lt.Lt h₀_lt h₁_lt
  simp_all


-- created on 2025-09-29
