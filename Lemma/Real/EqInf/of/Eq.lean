import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Macro.Order.ExprWithLimits
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


-- created on 2021-08-01
-- updated on 2026-10-17
