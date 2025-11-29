import Lemma.Bool.EqCast.of.SEq
import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.Tensor.DataSelect.as.FlattenGetSliceSplitAtData.of.GtLength
import sympy.tensor.tensor
open List Bool Tensor


@[main]
private lemma simp
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select d i).data = cast
    (by simp [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength d.isLt i.isLt])
    (X.data.splitAt (d + 1))[i : (s.take (d + 1)).prod:s[d]].flatten := by
-- proof
  apply Eq_Cast.of.SEq
  apply DataSelect.as.FlattenGetSliceSplitAtData.of.GtLength.simp


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select d i).data = cast
    (by simp [MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength d.isLt i.isLt])
    (X.data.splitAt (d + 1))[i :: s[d]].flatten := by
-- proof
  apply simp


-- created on 2025-11-07
-- updated on 2025-11-29
