import sympy.sets.sets
import Lemma.Algebra.LeNegS.of.Ge
open Algebra


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x a b : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  -x ∈ Icc (-b) (-a) := by
-- proof
  -- Start with the given inequalities from `h : x ∈ Icc a b`
  have h₀ : a ≤ x := h.left
  have h₁ : x ≤ b := h.right
  -- Apply negation to both sides of each inequality
  have h₂ : -x ≤ -a := LeNegS.of.Ge h₀
  have h₃ : -b ≤ -x := LeNegS.of.Ge h₁
  -- Combine the resulting inequalities to conclude membership in `Icc (-b) (-a)`
  exact ⟨h₃, h₂⟩


-- created on 2025-04-04
