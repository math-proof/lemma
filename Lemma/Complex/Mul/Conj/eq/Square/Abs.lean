import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {x : ℂ} :
-- imply
  x * ~x = ‖x‖ ^ 2 :=
-- proof
  Complex.mul_conj' x


-- created on 2023-05-25
