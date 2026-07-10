import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GetFromVector.eq.Get
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEqResize.of.GtVal_0
import Lemma.Tensor.SEqResizeS.of.SEq.EqValS.Eq
import Lemma.Tensor.SEqResize_0.of.GtLength_0
open Bool List Tensor


@[main, cast]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (h_i : i < s.length)
  (X : Tensor α s) :
-- imply
  X.resize ⟨i, by grind⟩ s[i] ≃ X := by
-- proof
  induction i generalizing X s with
  | zero =>
    apply SEqResize_0.of.GtLength_0
  | succ i ih =>
    rw [Resize.eq.Cast.of.GtVal_0 _ (by simp)]
    have h_s := EqCons_Tail.of.GtLength_0 (show s.length > 0 by grind)
    apply SEqCast.of.SEq.Eq
    ·
      rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
      simpa
    ·
      simp
      apply SEq.of.All_SEqGetS.Eq.GtLength_0 (by simp)
      ·
        intro t
        rw [GetFromVector.eq.Get.fin]
        simp
        erw [GetToVector.eq.Get.fin (i := ⟨t, by grind⟩)]
        have ih := ih (by grind) (X.get ⟨t, by grind⟩)
        simp at ih
        symm
        apply ih.symm.trans
        apply SEqResizeS.of.SEq.EqValS.Eq
        ·
          grind
        ·
          rfl
        ·
          rfl
      ·
        rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
        simpa


-- created on 2026-07-10
