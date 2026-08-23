import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {z : ℂ}
  {r : ℝ}
-- given
  (h : r > 0) :
-- imply
  arg (↑r * z) = arg z :=
-- proof
  Complex.arg_real_mul z h


-- created on 2018-08-25
-- updated on 2026-08-20
