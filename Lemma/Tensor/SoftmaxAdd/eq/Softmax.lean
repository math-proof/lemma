import Lemma.Tensor.DataAdd.eq.AddData
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data.of.GtLength
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.ExpAdd.eq.MulExpS
import Lemma.Tensor.Softmax.eq.One.of.LeLength
import Lemma.Vector.ExpAdd.eq.MulExpS
open Tensor Vector


@[main]
private lemma main
  [ExpRing α]
-- given
  (X : Tensor α s)
  (δ : α)
  (d : ℕ) :
-- imply
  (X + δ).softmax d = X.softmax d := by
-- proof
  if h : s.length > d then
    unfold Tensor.softmax
    simp
    apply Eq.of.EqDataS
    simp [DataDiv.eq.DivDataS]
    simp [DataExp.eq.ExpData]
    simp [DataKeepdim.eq.Cast_FlattenMapSplitAtCast_Data.of.GtLength h]
    simp [DataAdd.eq.AddData]
    simp [@Vector.ExpAdd.eq.MulExpS.scalar]
    simp [@Tensor.ExpAdd.eq.MulExpS.scalar]
    sorry
  else
    repeat rw [Softmax.eq.One.of.LeLength (by omega)]


-- created on 2025-11-30
-- updated on 2025-12-01
