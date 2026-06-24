import Lemma.List.Drop.eq.ListGet.of.GtLength_0
import Lemma.List.Drop.eq.ListGetS.of.GeLength_2
import Lemma.List.EqAppendS.of.Eq
import Lemma.List.EqAppendTake__Drop
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.Nat.EqAddMulDiv
import stdlib.SEq
import sympy.tensor.tensor
open List Nat


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α ((b :: bz) ++ [m, k]))
  (Y : Tensor α ((b :: bz) ++ [k, n]))
  (i : Fin b) :
-- imply
  (X.batch_dot Y).get i ≃ (X.get i).batch_dot (Y.get i) := by
-- proof
  simp [Tensor.batch_dot]
  sorry


-- created on 2026-06-24
