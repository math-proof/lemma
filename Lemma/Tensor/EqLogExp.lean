import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataLog.eq.LogData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqLogExp
open Vector Tensor


@[main]
private lemma main
  [LogPos α]
-- given
  (X : Tensor α s) :
-- imply
  log (exp X) = X := by
-- proof
  apply Eq.of.EqDataS
  rw [DataLog.eq.LogData]
  rw [DataExp.eq.ExpData]
  apply EqLogExp


-- created on 2025-12-04
