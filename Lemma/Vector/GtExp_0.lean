import Lemma.Real.GtExp_0
import Lemma.Vector.EqGet0_0
import sympy.vector.functions
open Real Vector


@[main]
private lemma main
  [ExpPos α]
-- given
  (x : List.Vector α n) :
-- imply
  exp x > 0 := by
-- proof
  intro i
  simp [Exp.exp, GetElem.getElem, EqGet0_0.fin]
  exact GtExp_0 x[i]


-- created on 2026-07-27
