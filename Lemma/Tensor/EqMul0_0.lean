import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqMul0_0
open Vector Tensor


@[main]
private lemma main
  [MulZeroClass α]
-- given
  (s : List ℕ)
  (a : α) :
-- imply
  (0 : Tensor α s) * a = 0 := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulData]
  rw [EqData0'0]
  apply EqMul0_0


-- created on 2025-12-23
