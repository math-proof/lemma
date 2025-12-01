import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Cast_Mul.eq.MulCastS.of.Eq
open Vector Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (h : s = s')
  (A B : Tensor α s) :
-- imply
  have h := congrArg (Tensor α) h
  cast h (A * B) = cast h A * cast h B := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulDataS]
  simp [DataCast.eq.Cast_Data.of.Eq h]
  rw [DataMul.eq.MulDataS]
  rw [Cast_Mul.eq.MulCastS.of.Eq]
  rw [h]


-- created on 2025-12-01
