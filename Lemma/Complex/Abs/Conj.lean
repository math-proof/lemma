import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {x y : ℂ} :
-- imply
  ‖x + ~y‖ = ‖~(x + ~y)‖ :=
-- proof
  (Complex.norm_conj _).symm


-- created on 2023-06-24
