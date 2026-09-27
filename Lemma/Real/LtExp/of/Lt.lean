import Lemma.Real.LtExpS.is.Lt
import sympy.functions.elementary.exponential
import sympy.Basic
open Real


@[main]
private lemma main
  [ExpPos α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  exp x < exp y :=
-- proof
  LtExpS.of.Lt h


-- created on 2026-09-26
