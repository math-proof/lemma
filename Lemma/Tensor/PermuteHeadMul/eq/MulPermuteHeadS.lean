import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.RotateMul.eq.MulRotateS
import Lemma.Tensor.TensorMul.eq.MulTensorS
import Lemma.Vector.Cast_Mul.eq.MulCastS.of.Eq
import Lemma.Vector.FlattenMul.eq.MulFlattenS
import Lemma.Vector.SplitAtMul.eq.MulSplitAtS
open List Tensor Vector


@[main]
private lemma main
  [Mul α]
-- given
  (A B : Tensor α s)
  (d : ℕ) :
-- imply
  (A * B).permuteHead d = A.permuteHead d * B.permuteHead d := by
-- proof
  simp [Tensor.permuteHead]
  apply Eq.of.EqDataS
  simp [DataMul.eq.MulDataS]
  rw [SplitAtMul.eq.MulSplitAtS]
  rw [TensorMul.eq.MulTensorS]
  rw [RotateMul.eq.MulRotateS]
  simp [DataMul.eq.MulDataS]
  rw [FlattenMul.eq.MulFlattenS]
  rw [@Vector.Cast_Mul.eq.MulCastS.of.Eq]
  rw [ProdAppend.eq.MulProdS]


-- created on 2025-12-02
-- updated on 2025-12-03
