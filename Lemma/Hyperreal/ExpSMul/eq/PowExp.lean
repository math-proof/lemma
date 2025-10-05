import sympy.functions.elementary.exponential
import sympy.Basic


@[main, comm]
private lemma main
-- given
  (x : ℝ*)
  (n : ℕ) :
-- imply
  (n • x).exp = x.exp ^ n :=
-- proof
  MonoidHom.map_pow Hyperreal.expMonoidHom _ _


-- created on 2025-10-05
