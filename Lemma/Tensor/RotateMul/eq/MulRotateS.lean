import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.TensorMul.eq.MulTensorS
import Lemma.Vector.Cast_Mul.eq.MulCastS.of.Eq
import Lemma.Vector.FlattenMul.eq.MulFlattenS
import Lemma.Vector.SplitAtMul.eq.MulSplitAtS
import Lemma.Vector.TransposeMul.eq.MulTransposeS
open List Tensor Vector


@[main]
private lemma main
  [Mul α]
-- given
  (A B : Tensor α s)
  (i : ℕ) :
-- imply
  (A * B).rotate i = A.rotate i * B.rotate i := by
-- proof
  simp [Tensor.rotate]
  simp [DataMul.eq.MulDataS]
  rw [SplitAtMul.eq.MulSplitAtS]
  rw [TransposeMul.eq.MulTransposeS]
  rw [FlattenMul.eq.MulFlattenS]
  rw [@Vector.Cast_Mul.eq.MulCastS.of.Eq]
  ·
    rw [TensorMul.eq.MulTensorS]
  ·
    rw [MulProdS.eq.ProdAppend]
    rw [Rotate.eq.AppendDrop__Take]


-- created on 2025-12-03
