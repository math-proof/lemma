import Lemma.Nat.Le.ou.Gt
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.List.TailSet_0.eq.Tail
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqMul1
import Lemma.Nat.LtMulS.of.Le.Lt.Gt_0.Gt_0
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Resize_0.as.AppendCast_Repeat_0.of.GtLength_0
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqResize_0.of.Eq_Get_0.GtLength_0
open Bool List Nat Tensor
set_option maxHeartbeats 4000000


@[main, fin, cast, cast.fin]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0])
  (n : ℕ) :
-- imply
  (X.resize ⟨0, by grind⟩ (s[0] ⊔ n))[i]'(by rw [Length.eq.Get_0.of.GtLength_0 (by grind)]; grind) ≃ X[i]'(GtLength.of.GtLength_0 h X i) := by
-- proof
  obtain h_le | h_lt := Le.ou.Gt s[0] n
  ·
    have h_size : s[0] ⊔ n = n := by grind
    have := Resize_0.eq.Cast_AppendCast_Repeat_0.of.GtLength_0 h X (s[0] ⊔ n)
    have := EqGetS.of.Eq.GtLength_0 (by grind) this ⟨i, by grind⟩
    simp at this
    have := SEq.of.Eq this
    apply this.trans
    erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (i := ⟨i, by grind⟩) (by grind)]
    apply SEqCast.of.SEq.Eq (by simp [TailSet_0.eq.Tail])
    simp
    have h_div : n / s[0] > 0 := by simp; grind
    have h_lt : i < n / s[0] * s[0] := by
      if h_i : i = ⟨0, by grind⟩ then
        subst h_i
        simp
        grind
      else
        rw [← EqMul1 i.val]
        apply LtMulS.of.Le.Lt.Gt_0.Gt_0
        ·
          simp
          grind
        ·
          simp
          grind
        ·
          grind
        ·
          simp
    rw [GetAppend.eq.Get.of.Lt.fin]
    ·
      erw [GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin (i := ⟨i, by simpa [h_size]⟩) (by grind)]
      apply SEqCast.of.SEq.Eq (by simp [TailSet_0.eq.Tail])
      ·
        simp
        erw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin (by grind) (by grind)]
        apply SEqCast.of.SEq.Eq (by simp [TailSet_0.eq.Tail])
        simp [EqMod.of.Lt i.isLt]
        rfl
      ·
        simp [h_size]
        rw [Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]
    ·
      simpa [h_size]
    ·
      simp [h_size]
      rw [Set_0.eq.Cons_Tail.of.GtLength_0 (by grind)]
      simp [EqAddMulDiv]
  ·
    apply SEqGetS.of.SEq.GtLength.fin _
    apply SEqResize_0.of.Eq_Get_0.GtLength_0 h
    grind


-- created on 2026-07-09
-- updated on 2026-07-19
