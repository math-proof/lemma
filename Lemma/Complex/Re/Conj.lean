import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {z : ℂ} :
-- imply
  re z = re (~z) :=
-- proof
  (Complex.conj_re z).symm


-- created on 2023-06-24
