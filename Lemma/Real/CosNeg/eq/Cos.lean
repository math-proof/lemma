import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  Cos.cos (-x) = Cos.cos x :=
-- proof
  Real.cos_neg x


-- created on 2026-09-03
