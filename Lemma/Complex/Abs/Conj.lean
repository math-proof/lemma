import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {x y : ℂ} :
-- imply
  ‖x + ~y‖ = ‖~(x + ~y)‖ :=
-- proof
  (Complex.norm_conj _).symm


-- created on 2026-09-27
