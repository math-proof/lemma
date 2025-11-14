import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.List.LengthSlice.eq.Min
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetGetSlice.eq.Get
import Lemma.Nat.LtVal
open Tensor List Nat


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
    rw [GetGetSlice.eq.Get.fin]
    rw [EqGetStack.fin]
  .
    simp [Tensor.length]
    rw [LengthSlice.eq.Min]
    simp


-- created on 2025-10-01
