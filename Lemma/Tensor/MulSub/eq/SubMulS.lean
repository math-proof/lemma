import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataSub.eq.SubDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.MulSub.eq.SubMulS
open Tensor Vector


@[main, comm]
private lemma main
  [NonUnitalNonAssocRing α]
-- given
  (A B : Tensor α s)
  (x : α) :
-- imply
  (A - B) * x = A * x - B * x := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulData]
  repeat rw [DataSub.eq.SubDataS]
  repeat rw [DataMul.eq.MulData]
  rw [MulSub.eq.SubMulS]


-- created on 2025-12-29
