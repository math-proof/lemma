import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Cast_Mul.eq.MulCast.of.Eq
open Tensor Vector


@[main]
private lemma main
  [Mul α]
-- given
  (h : s = s')
  (X : Tensor α s)
  (a : α) :
-- imply
  have h := congrArg (Tensor α) h
  cast h (X * a) = cast h X * a := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulData]
  simp [DataCast.eq.Cast_Data.of.Eq h]
  rw [DataMul.eq.MulData]
  rw [Cast_Mul.eq.MulCast.of.Eq]
  rw [h]


-- created on 2025-12-01
