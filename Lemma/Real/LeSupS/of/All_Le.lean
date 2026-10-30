import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Syntax.Order.ExprWithLimits
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f g : α → ℝ}
  {S : Set α}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddAbove (g '' S))
  (h₂ : ∀ x ∈ S, f x ≤ g x) :
-- imply
  sSup (f '' S) ≤ sSup (g '' S) := by
-- proof
  apply csSup_le (h₀.image f)
  rintro _ ⟨x, hx, rfl⟩
  apply (h₂ x hx).trans
  apply le_csSup h₁
  apply Set.mem_image_of_mem
  exact hx


-- created on 2023-04-23
-- updated on 2026-10-26
