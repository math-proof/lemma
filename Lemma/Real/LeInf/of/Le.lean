import Mathlib.Order.ConditionallyCompleteLattice.Basic
import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  {f g : α → ℝ}
  {S : Set α}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddBelow (f '' S))
  (h₂ : ∀ x ∈ S, f x ≤ g x) :
-- imply
  sInf (f '' S) ≤ sInf (g '' S) := by
-- proof
  apply le_csInf (h₀.image g)
  rintro _ ⟨x, hx, rfl⟩
  apply le_trans
  · apply csInf_le h₁
    apply Set.mem_image_of_mem f
    exact hx
  · exact h₂ x hx


-- created on 2026-10-11
-- updated on 2026-10-17
