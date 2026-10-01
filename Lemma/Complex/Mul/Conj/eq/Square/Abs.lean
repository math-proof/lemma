import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {x : ℂ} :
-- imply
  x * ~x = ‖x‖ ^ 2 :=
-- proof
  Complex.mul_conj' x


-- created on 2026-09-27
