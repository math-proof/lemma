import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {x : ℂ} :
-- imply
  ‖x‖ ^ 2 = x * ~x :=
-- proof
  (Complex.mul_conj' x).symm


-- created on 2026-09-27
