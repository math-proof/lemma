import Lemma.Real.EqLogExp
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.GetLog.eq.LogGet
open Real Vector


@[main]
private lemma main
  [LogPos α]
-- given
  (x : List.Vector α n) :
-- imply
  log (exp x) = x := by
-- proof
  ext i
  rw [GetLog.eq.LogGet.fin]
  rw [GetExp.eq.ExpGet.fin]
  apply EqLogExp


-- created on 2025-12-04
