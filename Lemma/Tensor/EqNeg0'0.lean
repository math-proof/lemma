import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqNeg0'0
import sympy.tensor.tensor
open Vector Tensor


@[main]
private lemma main
  [AddGroupWithOne α]
  {s : List ℕ} :
-- imply
  -((0 : ℕ) : Tensor α s) = 0 := by
-- proof
  apply Eq.of.EqDataS
  rw [DataNeg.eq.NegData]
  rw [EqData0'0]
  apply EqNeg0'0


-- created on 2026-09-04
