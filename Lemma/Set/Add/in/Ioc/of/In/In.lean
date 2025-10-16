import sympy.sets.sets
import Lemma.Nat.LtAddS.of.Lt.Lt
import Lemma.Algebra.LeAddS.of.Le.Le
open Algebra Nat


@[main]
private lemma main
  [Preorder α]
  [Add α]
  [AddRightStrictMono α]
  [AddLeftStrictMono α]
  [AddRightMono α]
  [AddLeftMono α]
  {a b c d x₀ x₁ : α}
-- given
  (h₀ : x₀ ∈ Ioc a b)
  (h₁ : x₁ ∈ Ioc c d) :
-- imply
  x₀ + x₁ ∈ Ioc (a + c) (b + d) := by
-- proof
  let ⟨h₀_gt, h₀_le⟩ := h₀
  let ⟨h₁_gt, h₁_le⟩ := h₁
  have h_gt := LtAddS.of.Lt.Lt h₀_gt h₁_gt
  have h_le := LeAddS.of.Le.Le h₀_le h₁_le
  simp_all


-- created on 2025-09-29
