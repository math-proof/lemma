import torch.Tensor.permute
import Lemma.Tensor.RotateMul.eq.MulRotateS
import Lemma.Vector.MapMul.eq.MulMapS.of.All_Eq_Mul
open List Tensor Vector


@[path]
private lemma main
  [Mul α]
-- given
  (A B : Tensor α s)
  (d : ℕ) :
-- imply
  (A * B).permuteTail d = A.permuteTail d * B.permuteTail d := by
-- proof
  simp [Tensor.permuteTail]
  apply Eq.of.EqDataS
  simp [DataMul.eq.MulDataS]
  rw [SplitAtMul.eq.MulSplitAtS]
  rw [MapMul.eq.MulMapS.of.All_Eq_Mul]
  ·
    rw [FlattenMul.eq.MulFlattenS]
    rw [@Vector.Cast_Mul.eq.MulCastS.of.Eq]
    rw [ProdAppend.eq.MulProdS]
  ·
    intro a b
    rw [TensorMul.eq.MulTensorS]
    rw [RotateMul.eq.MulRotateS]
    simp [DataMul.eq.MulDataS]


-- created on 2025-12-03
