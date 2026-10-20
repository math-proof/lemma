import Mathlib.Order.ConditionallyCompleteLattice.Basic
import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  {f g : α → ℝ}
  {S : Set α}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddBelow (g '' S))
  (h₂ : ∀ x ∈ S, g x ≤ f x) :
-- imply
  Minima S g ≤ Minima S f := by
-- proof
  apply le_csInf (h₀.image f)
  rintro _ ⟨x, hx, rfl⟩
  apply le_trans
  · apply csInf_le h₁
    apply Set.mem_image_of_mem g
    exact hx
  · exact h₂ x hx


-- created on 2023-04-23
-- updated on 2026-10-17
