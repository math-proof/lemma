import Lemma.Complex.EqIm0'0
import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {z : ℂ}
-- given
  (h : z = 0) :
-- imply
  im z = 0 :=
-- proof
  h.symm.subst (motive := fun z => im z = 0) Complex.EqIm0'0


-- created on 2025-01-17
