import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Macro.Order.ExprWithLimits
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : α → ℝ}
  {S : Set α}
  {M : ℝ}
-- given
  (h₀ : BddBelow (f '' S))
  (h₁ : M < Minima S f) :
-- imply
  ∀ x ∈ S, M < f x := by
-- proof
  intro x hx
  apply lt_of_lt_of_le h₁
  apply csInf_le h₀
  apply Set.mem_image_of_mem
  exact hx


-- created on 2023-11-12
-- updated on 2026-10-26
