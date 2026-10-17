import Mathlib.Order.ConditionallyCompleteLattice.Basic
import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  {f : α → ℝ}
  {S : Set α}
  {M : ℝ}
-- given
  (h₀ : BddBelow (f '' S))
  (h₁ : M ≤ Minima S f) :
-- imply
  ∀ x ∈ S, M ≤ f x := by
-- proof
  intro x hx
  apply h₁.trans
  apply csInf_le h₀
  apply Set.mem_image_of_mem
  exact hx


-- created on 2026-10-11
-- updated on 2026-10-17
