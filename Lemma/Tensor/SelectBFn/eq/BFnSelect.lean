import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.MapGetSlice.eq.GetSliceMap
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
import sympy.tensor.tensor
open List Tensor Vector


@[main]
private lemma main
-- given
  (f : α → α → α)
  (X : Tensor α s)
  (B : Tensor α [])
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (X.map (f · B.data[0])).select d i = (X.select d i).map (f · B.data[0]) := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.select Tensor.map
  let g := (f · B.data[0])
  let hprod := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp d.isLt i.isLt
  rw [MapCast.eq.Cast_Map.of.Eq hprod]
  apply congrArg (cast (congrArg (List.Vector α) hprod))
  rw [SplitAtMap.eq.MapSplitAt]
  rw [← MapGetSlice.eq.GetSliceMap]
  apply FlattenMap.eq.MapFlatten


-- created on 2026-08-15
