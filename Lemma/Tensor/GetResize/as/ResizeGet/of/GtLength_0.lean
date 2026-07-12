import Lemma.Bool.SEqCast.of.Eq
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.LengthResize.eq.Get_0
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
open Bool Tensor


@[main, fin, cast, cast.fin]
private lemma main
  [Zero α]
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (d : Fin s.length)
  (h_d : d.val > 0)
  (n : ℕ)
  (i : Fin s[0]) :
-- imply
  have := LengthResize.eq.Get_0 X ⟨0, by grind⟩
  have := GtLength.of.GtLength_0 h X i
  (X.resize d n)[i]'(by grind) ≃ X[i].resize ⟨d - 1, by grind⟩ n := by
-- proof
  have := Resize_0.eq.Cast.of.Eq_Get_0.GtLength_0 h (by grind) X (n := s[0] ⊔ s[0])
  simp [this]
  simp only [GetElem.getElem]
  rw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) (by simp)]
  apply SEqCast.of.Eq
  simp


-- created on 2026-07-12
