import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  (S : Set α)
  (f : α → ℝ) :
-- imply
  sSup (f '' S) ≥ Maxima S f :=
-- proof
  le_rfl


-- created on 2026-10-11
-- updated on 2026-10-17
