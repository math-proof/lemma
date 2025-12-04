import Lemma.Vector.Sub.eq.Add_Neg
import Lemma.Tensor.DataAdd.eq.AddData
import Lemma.Tensor.DataSub.eq.SubData
import Lemma.Tensor.Eq.is.EqDataS
open Vector Tensor


@[main, comm]
private lemma main
  [SubNegMonoid α]
-- given
  (X : Tensor α s)
  (a : α) :
-- imply
  X - a = X + -a := by
-- proof
  apply Eq.of.EqDataS
  rw [DataAdd.eq.AddData]
  rw [DataSub.eq.SubData]
  rw [Sub.eq.Add_Neg]


-- created on 2025-12-04
