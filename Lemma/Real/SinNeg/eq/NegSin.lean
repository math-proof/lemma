import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  Sin.sin (-x) = -Sin.sin x :=
-- proof
  Real.sin_neg x


-- created on 2026-09-03
