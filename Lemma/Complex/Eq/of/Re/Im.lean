import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {z w : ℂ}
-- given
  (h_Re : re z = re w)
  (h_Im : im z = im w) :
-- imply
  z = w :=
-- proof
  Complex.ext h_Re h_Im


-- created on 2025-01-17
