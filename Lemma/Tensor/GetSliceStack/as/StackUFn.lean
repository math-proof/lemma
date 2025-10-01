import sympy.tensor.stack
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.Algebra.LengthSlice.eq.Min
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetGetSlice.eq.Get.of.Lt_Min_Length
open Tensor Algebra


@[main]
private lemma main
-- given
  (f : ℕ → Tensor α s)
  (n j : ℕ):
-- imply
  ([i < n + j] f i)[:n] ≃ [i < n] f i := by
-- proof
  apply SEq.of.All_SEqGetS.Eq.Eq
  .
    aesop
  .
    intro j
    simp only [GetElem.getElem]
    simp [EqGetStack.fin]
    rw [GetGetSlice.eq.Get.of.Lt_Min_Length.fin]
    .
      rw [EqGetStack.fin]
    .
      simp [Tensor.length]
      have h_j := LtVal j
      simp only [Tensor.length] at h_j
      simp [LengthSlice.eq.Min] at h_j
      assumption
  .
    simp [Tensor.length]
    rw [LengthSlice.eq.Min]
    simp


-- created on 2025-10-01
