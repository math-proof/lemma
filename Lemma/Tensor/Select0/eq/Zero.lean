import torch.Tensor.select
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqSplitAt0_0
import Lemma.Vector.GetSlice0.eq.Zero
import Lemma.Vector.Flatten0.eq.Zero
import Lemma.Vector.EqCast_0'0.of.Eq
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
open Tensor Vector


@[main]
private lemma main
  [Zero α]
  {s : List ℕ}
  {o : Fin s.length}
-- given
  (i : Fin s[o]) :
-- imply
  (0 : Tensor α s).select o i = 0 := by
-- proof
  apply Eq.of.EqDataS
  simp only [Tensor.select, EqData0'0, EqSplitAt0_0]
  simp [GetSlice0.eq.Zero, Flatten0.eq.Zero]
  exact EqCast_0'0.of.Eq
    (List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp o.isLt i.isLt)


-- created on 2026-09-16
