import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.MapGetSlice.eq.GetSliceMap
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
import sympy.tensor.tensor
open List Tensor Vector


@[main, comm]
private lemma main
  {f : α → β}
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (X.map f).select d i = (X.select d i).map f := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.select Tensor.map
  let hprod := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp d.isLt i.isLt
  rw [MapCast.eq.Cast_Map.of.Eq hprod]
  apply congrArg (cast (congrArg (List.Vector β) hprod))
  rw [SplitAtMap.eq.MapSplitAt]
  rw [← MapGetSlice.eq.GetSliceMap]
  apply FlattenMap.eq.MapFlatten


-- created on 2026-08-17
