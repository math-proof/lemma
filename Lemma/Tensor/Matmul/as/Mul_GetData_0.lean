import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.List.Eq_Nil.is.EqLength_0
import Lemma.Fin.Eq_0
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.DataMul.eq.Mul_Data
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetMul.eq.Mul_Get
import sympy.tensor.tensor
open List Tensor Vector Fin Bool


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α s)
  (Y : Tensor α []) :
-- imply
  X.matmul Y ≃ X * Y.data[0] := by
-- proof
  apply SEq.of.Eq_Cast
  .
    unfold Tensor.matmul
    simp
    split_ifs with h_s
    ·
      apply EqCastS.of.SEq.Eq
      .
        simp [Tensor.matmul_shape]
      .
        subst h_s
        apply SEq.of.Eq
        apply Eq.of.EqDataS
        rw [DataMul.eq.MulData]
        rw [DataMul.eq.Mul_Data]
        apply Eq.of.All_EqGetS
        intro i
        have h_i := Eq_0 i
        subst h_i
        rw [GetMul.eq.MulGet]
        rw [GetMul.eq.Mul_Get]
        rfl
    ·
      simp
  .
    simp [Tensor.matmul_shape]


-- created on 2026-01-06
