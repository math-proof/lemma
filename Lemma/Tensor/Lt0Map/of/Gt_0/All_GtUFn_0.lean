import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Lt.is.LtDataS
import Lemma.Tensor.MapData.eq.DataMap
import Lemma.Vector.EqGet0_0
import Lemma.Vector.Lt.is.All_Lt
open Tensor Vector


@[main]
private lemma main
  [Preorder α] [Preorder β] [Zero α] [Zero β]
  {f : α → β}
  {X : Tensor α s}
-- given
  (h_f : ∀ a > 0, f a > 0)
  (h : X > 0) :
-- imply
  X.map f > 0 := by
-- proof
  rw [gt_iff_lt, Lt.is.LtDataS, EqData0'0]
  rw [← MapData.eq.DataMap]
  rw [Lt.is.All_Lt]
  intro i
  simp [GetElem.getElem, EqGet0_0.fin]
  apply h_f
  have h := LtDataS.of.Lt (gt_iff_lt.mp h)
  rw [EqData0'0, Lt.is.All_Lt] at h
  simpa [GetElem.getElem, EqGet0_0.fin] using h i


-- created on 2026-08-16
