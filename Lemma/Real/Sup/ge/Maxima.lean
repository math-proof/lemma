import Syntax.Order.ExprWithLimits
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (S : Set α)
  (f : α → ℝ) :
-- imply
  sSup (f '' S) ≥ Maxima S f :=
-- proof
  le_rfl


-- created on 2019-09-21
-- updated on 2026-10-26
