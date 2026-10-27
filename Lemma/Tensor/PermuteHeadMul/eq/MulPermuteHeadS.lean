import Notation.Data.Holor.Permute
import Lemma.Tensor.RotateMul.eq.MulRotateS
open List Tensor Vector


@[path]
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
-- updated on 2026-10-26
