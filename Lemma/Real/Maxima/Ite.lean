import Mathlib.Order.ConditionallyCompleteLattice.Basic
import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  {f : α → ℝ}
  {S : Set α}
  {c : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddAbove (f '' S))
  (h₂ : c ≤ Maxima S f) :
-- imply
  sSup (insert c (f '' S)) = Maxima S f := by
-- proof
  rw [csSup_insert h₁ (h₀.image f)]
  apply max_eq_right h₂


-- created on 2023-04-23
-- updated on 2026-10-17
