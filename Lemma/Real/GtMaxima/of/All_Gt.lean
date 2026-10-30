import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Syntax.Order.ExprWithLimits
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : α → ℝ}
  {S : Set α}
  {m : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddAbove (f '' S))
  (h₂ : ∀ x ∈ S, m < f x) :
-- imply
  m < Maxima S f := by
-- proof
  obtain ⟨x, hx⟩ := h₀
  apply lt_of_lt_of_le (h₂ x hx)
  apply le_csSup h₁
  apply Set.mem_image_of_mem
  exact hx


-- created on 2023-03-25
-- updated on 2026-10-26
