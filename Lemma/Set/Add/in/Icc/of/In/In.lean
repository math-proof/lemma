import sympy.sets.sets
import Lemma.Nat.LeAddS.of.Le.Le
open Nat


@[main]
private lemma main
  [Preorder α]
  [Add α]
  [AddRightMono α]
  [AddLeftMono α]
  {a b c d x₀ x₁ : α}
-- given
  (h₀ : x₀ ∈ Icc a b)
  (h₁ : x₁ ∈ Icc c d) :
-- imply
  x₀ + x₁ ∈ Icc (a + c) (b + d) := by
-- proof
  let ⟨h₀_ge, h₀_le⟩ := h₀
  let ⟨h₁_ge, h₁_le⟩ := h₁
  have h_gt := LeAddS.of.Le.Le h₀_ge h₁_ge
  have h_le := LeAddS.of.Le.Le h₀_le h₁_le
  simp_all


-- created on 2025-09-29
