import Mathlib.Order.ConditionallyCompleteLattice.Basic
import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  {f g : α → ℝ}
  {S : Set α}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddAbove (f '' S))
  (h₂ : ∀ x ∈ S, g x ≤ f x) :
-- imply
  Maxima S g ≤ Maxima S f := by
-- proof
  apply csSup_le (h₀.image g)
  rintro _ ⟨x, hx, rfl⟩
  apply (h₂ x hx).trans
  apply le_csSup h₁
  apply Set.mem_image_of_mem
  exact hx


-- created on 2026-10-11
-- updated on 2026-10-17
