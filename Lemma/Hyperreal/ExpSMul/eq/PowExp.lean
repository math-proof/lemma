import sympy.functions.elementary.exponential
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ*)
  (n : ℕ) :
-- imply
  exp (n • x) = exp x ^ n :=
-- proof
  MonoidHom.map_pow Hyperreal.expMonoidHom _ _


-- created on 2025-10-05
