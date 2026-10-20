import Mathlib.Order.ConditionallyCompleteLattice.Basic
import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  {f g : α → ℝ}
  {S : Set α}
-- given
  (h₀ : ∀ x ∈ S, f x = g x) :
-- imply
  sSup (f '' S) = sSup (g '' S) := by
-- proof
  apply congrArg sSup
  apply Set.image_congr h₀


-- created on 2021-09-16
-- updated on 2026-10-17
