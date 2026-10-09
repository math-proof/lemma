import sympy.Basic
import sympy.concrete.expr_with_limits
import Mathlib.Algebra.Order.Archimedean.Real.Basic


@[path]
private lemma main
  {S : Set α}
  {f : α → ℝ}
  {M : ℝ}
-- given
  (h₀ : M = Minima S f)
  (h₁ : BddBelow (f '' S)) :
-- imply
  ∀ x ∈ S, M ≤ f x := by
-- proof
  intro x hx
  rw [h₀]
  exact csInf_le h₁ ⟨x, hx, rfl⟩


-- created on 2019-01-16
