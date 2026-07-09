import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Tensor.LengthResize.eq.Get_0
import Lemma.Tensor.SEqResize_0.of.GtLength_0
open Bool Tensor List Nat Vector


@[main, cast]
private lemma main
  [Zero α]
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have := LengthResize.eq.Get_0 X ⟨0, by grind⟩
  have := Tensor.GtLength.of.GtLength_0 h X i
  (X.resize ⟨0, by grind⟩ (s[0] ⊔ s[0]))[i]'(by grind) ≃ X[i] := by
-- proof
  have := Resize_0.eq.Cast.of.GtLength_0 h X
  simp [this]
  simp only [GetElem.getElem]
  rw [Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) (by simp)]
  apply SEqCast.of.Eq
  simp


-- created on 2026-07-09
