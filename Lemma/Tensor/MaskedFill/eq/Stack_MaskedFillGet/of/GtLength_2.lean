import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetMaskedFill.eq.MaskedFillGet.of.GtLength_2
import Lemma.Tensor.GtLength.of.GtLength_0
open Tensor


@[main, fin]
private lemma main
  [Zero α]
-- given
  (h : s.length ≥ 2)
  (X : Tensor α (n :: s))
  (d : ℤ)
  (cmp : ℤ → ℤ → Bool) :
-- imply
  X.masked_fill d cmp = [i < n] (X[i].masked_fill d cmp) := by
-- proof
  simp [GetElem.getElem]
  apply Eq.of.All_EqGetS.fin
  intro i
  erw [GetMaskedFill.eq.MaskedFillGet.of.GtLength_2.fin (by grind)]
  conv_rhs => erw [EqGetStack.fn.fin (i := ⟨i, by grind⟩)]
  rfl


-- created on 2026-07-29
