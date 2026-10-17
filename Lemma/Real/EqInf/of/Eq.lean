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
  sInf (f '' S) = sInf (g '' S) := by
-- proof
  apply congrArg sInf
  apply Set.image_congr h₀


-- created on 2026-10-11
-- updated on 2026-10-17
