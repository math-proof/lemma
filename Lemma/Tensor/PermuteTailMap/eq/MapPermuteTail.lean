import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.MapData.eq.DataMap
import Lemma.Tensor.RotateMap.eq.MapRotate
import Lemma.Tensor.TensorMap.eq.MapTensor
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.MapMap.eq.Map_Comp
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
open List Tensor Vector


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (d : ℕ)
  (f : α → β):
-- imply
  (X.map f).permuteTail d = (X.permuteTail d).map f := by
-- proof
  simp [Tensor.permuteTail]
  apply Eq.of.EqDataS
  simp [Tensor.map]
  rw [SplitAtMap.eq.MapSplitAt, MapMap.eq.Map_Comp]
  conv_lhs =>
    pattern Function.comp _ _
    ext data
    simp only [Function.comp]
    rw [TensorMap.eq.MapTensor, RotateMap.eq.MapRotate, DataMap.eq.MapData]
  set split := X.data.splitAt (s.length - d)
  set rotateData := fun data => ((⟨data⟩ : Tensor α (s.drop (s.length - d))).rotate (d ⊓ s.length - 1)).data
  have h_map : split.map (fun data => (rotateData data).map f) = (split.map rotateData).map (fun row => row.map f) := by
    ext i
    simp only [List.Vector.get_map]
  have h_lhs : split.map (fun data : List.Vector α (s.drop (s.length - d)).prod => ((⟨data⟩ : Tensor α (s.drop (s.length - d))).rotate (d ⊓ s.length - 1)).data.map f) = (split.map rotateData).map (fun row => row.map f) :=
    Eq.trans (by rfl) h_map
  rw [h_lhs, FlattenMap.eq.MapFlatten]
  rw [MapCast.eq.Cast_Map.of.Eq]
  rw [MulProdS.eq.ProdAppend]


-- created on 2026-08-07
