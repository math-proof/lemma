import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.GetBmm.as.BmmGetS.of.Eq
import Lemma.Tensor.GetFromVector.eq.Get
import Lemma.Tensor.GetResize_0.as.Get.of.GtLength_0
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.SEqMatmulS.of.SEq.SEq
open Bool Tensor


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α (s ++ [m, k]))
  (Y : Tensor α (s ++ [k, n])) :
-- imply
  X.matmul Y (by simp) ≃ X.bmm Y := by
-- proof
  induction s generalizing m k n with
  | nil =>
    unfold matmul
    rfl
  | cons h t ih =>
    unfold matmul
    simp
    apply SEqCast.of.SEq.Eq (by simp [broadcast_shape])
    apply SEq.of.All_SEqGetS.Eq.GtLength_0 (by simp)
    ·
      intro j
      simp
      erw [GetBmm.eq.Cast_BmmGetS.of.Eq.fin (b₀ := h) (b := t) (by simp) (i := ⟨j, by grind⟩)]
      apply SEq_Cast.of.SEq.Eq (by simp)
      ·
        rw [GetFromVector.eq.Get.fin]
        simp
        have ih := ih (X.get ⟨j, by grind⟩) (Y.get ⟨j, by grind⟩)
        symm
        apply ih.symm.trans
        apply SEqMatmulS.of.SEq.SEq (by simp) <;>
        ·
          erw [GetToVector.eq.Get.fin]
          simp
          erw [GetResize_0.eq.Cast_Get.of.GtLength_0.fin (i := ⟨j, by grind⟩) (by grind)]
          simp
          rfl
    ·
      simp [broadcast_shape]


-- created on 2026-07-10
