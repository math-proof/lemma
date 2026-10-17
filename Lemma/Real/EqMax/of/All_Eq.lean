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
  Maxima S f = Maxima S g := by
-- proof
  rw [Maxima, Maxima]
  apply congrArg sSup
  apply Set.image_congr h₀


-- created on 2026-10-11
-- updated on 2026-10-17
