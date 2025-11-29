import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.ExpCast.eq.Cast_Exp.of.Eq
import Lemma.Vector.ExpFlatten.eq.FlattenExp
import Lemma.Vector.ExpGetSlice.eq.GetSliceExp.of.Lt.Dvd
import Lemma.Vector.ExpSplitAt.eq.SplitAtExp
import sympy.tensor.functions
open Bool List Tensor Vector


@[main, comm]
private lemma main
  [Exp α]
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (exp X).select d i = exp (X.select d i) := by
-- proof
  apply Eq.of.EqDataS
  conv_rhs => rw [DataExp.eq.ExpData]
  repeat rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.simp]
  have h_length_slice := MulLengthSlice_Mul.eq.ProdEraseIdx.of.Lt_Get.GtLength d.isLt i.isLt
  rw [ExpCast.eq.Cast_Exp.of.Eq]
  ·
    apply EqCastS.of.SEq.Eq
    ·
      simp [h_length_slice]
    ·
      apply SEq.of.Eq
      rw [ExpFlatten.eq.FlattenExp]
      congr
      rw [ExpGetSlice.eq.GetSliceExp.of.Lt.Dvd _ i.isLt]
      .
        congr
        rw [ExpSplitAt.eq.SplitAtExp]
        congr
      .
        simp [List.ProdTake.eq.MulProdTake.of.GtLength d.isLt]
  ·
    simp [h_length_slice]


-- created on 2025-11-17
-- updated on 2025-11-29
