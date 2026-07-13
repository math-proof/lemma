import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqMulDiv
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.Resize_0.as.AppendCast_Repeat_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
open Bool List Nat Tensor


@[main, cast]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.resize ⟨0, by grind⟩ s[0] ≃ X := by
-- proof
  rw [Resize_0.eq.Cast_AppendCast_Repeat_0.of.GtLength_0 h_s]
  simp
  apply SEqCast.of.SEq.Eq
  ·
    simp [EqMulDiv]
    rw [EqCons_Tail.of.GtLength_0]
  ·
    apply SEq.of.All_SEqGetS.Eq.GtLength_0 (by grind) (by simp [EqMulDiv, EqCons_Tail.of.GtLength_0])
    intro t
    have h_t := t.isLt
    simp [EqMulDiv] at h_t
    rw [GetAppend.eq.Get.of.Lt.fin]
    ·
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin (by grind) (by simp [EqMulDiv, EqCons_Tail.of.GtLength_0]) (i := ⟨t, by simp [EqMulDiv]; grind⟩)]
      simp
      apply SEqCast.of.SEq.Eq
      ·
        simp [EqMulDiv]
      ·
        rw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by simp [EqMulDiv]; grind)]
        apply SEqCast.of.SEq.Eq
        ·
          simp [EqMulDiv]
        ·
          simp [EqMod.of.Lt h_t]
          rfl
    ·
      simpa [EqMulDiv]


-- created on 2026-07-10
-- updated on 2026-07-13
