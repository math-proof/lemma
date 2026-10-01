import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {z : ℂ} :
-- imply
  re z = re (~z) :=
-- proof
  (Complex.conj_re z).symm


-- created on 2026-09-27
