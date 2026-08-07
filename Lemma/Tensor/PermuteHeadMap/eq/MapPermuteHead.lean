import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Tensor.MapData.eq.DataMap
import Lemma.Tensor.RotateMap.eq.MapRotate
import Lemma.Tensor.TensorMap.eq.MapTensor
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
import sympy.tensor.tensor
open List Tensor Vector


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (d : ℕ)
  (f : α → β):
-- imply
  (X.map f).permuteHead d = (X.permuteHead d).map f := by
-- proof
  unfold Tensor.permuteHead
  simp
  rw [DataMap.eq.MapData]
  rw [SplitAtMap.eq.MapSplitAt]
  rw [TensorMap.eq.MapTensor]
  rw [RotateMap.eq.MapRotate]
  rw [DataMap.eq.MapData]
  rw [FlattenMap.eq.MapFlatten]
  simp [Tensor.map]
  rw [MapCast.eq.Cast_Map.of.Eq]
  rw [MulProdS.eq.ProdAppend, Rotate.eq.AppendDrop__Take]


-- created on 2026-08-07
