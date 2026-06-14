import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength_0
open Tensor


@[main, fin]
private lemma main
  {s : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h_n : n = s[0])
  (X : Tensor α s)
  (i : Fin n) :
-- imply
  have h_s : n :: s.tail = s := h_n.symm ▸ List.EqCons_Tail.of.GtLength_0 h₀
  have := GtLength.of.GtLength_0 h₀ X ⟨i, by grind⟩
  (cast (congrArg (Tensor α) h_s.symm) X)[i] = cast (by grind) X[i] := by
-- proof
  intro h_s
  simp [GetElem.getElem]
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin h₀ h_s.symm X ⟨i, by grind⟩
  simp at this
  rw [this]


-- created on 2026-06-12
