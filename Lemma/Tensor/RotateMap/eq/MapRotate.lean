import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
import Lemma.Vector.TransposeMap.eq.MapTranspose
import sympy.tensor.Basic
open List Vector


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (d : ℕ)
  (f : α → β):
-- imply
  (X.map f).rotate d = (X.rotate d).map f := by
-- proof
  simp [Tensor.rotate, Tensor.map]
  rw [SplitAtMap.eq.MapSplitAt]
  rw [TransposeMap.eq.MapTranspose]
  rw [FlattenMap.eq.MapFlatten]
  rw [MapCast.eq.Cast_Map.of.Eq]
  rw [MulProdS.eq.ProdAppend, Rotate.eq.AppendDrop__Take]


-- created on 2026-08-07
