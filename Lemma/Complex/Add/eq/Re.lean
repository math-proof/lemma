import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {z w : ℂ} :
-- imply
  re z + re w = re (z + w) :=
-- proof
  (Complex.add_re z w).symm


-- created on 2026-09-27
