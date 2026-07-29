import Lemma.Tensor.EqMaskedFill.of.LtLength_2
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.MapStack.eq.StackMap
import Lemma.Tensor.MaskedFill.eq.Stack_MaskedFillGet.of.GtLength_2
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapMaskedFill.eq.MaskedFillMap.of.EqUFn0'0 |
| comm | Tensor.MaskedFillMap.eq.MapMaskedFill.of.EqUFn0'0 |
-/
@[main, comm]
private lemma main
  [Zero α]
  [Zero β]
  {f : α → β}
-- given
  (hf : f 0 = 0)
  (X : Tensor α s)
  (d : ℤ)
  (cmp : ℤ → ℤ → Bool) :
-- imply
  (X.masked_fill d cmp).map f = (X.map f).masked_fill d cmp := by
-- proof
  induction s with
  | nil =>
    unfold Tensor.masked_fill
    simp
  | cons n s ih =>
    if h_len_gt : (n :: s).length > 2 then
      rw [MaskedFill.eq.Stack_MaskedFillGet.of.GtLength_2 (by grind)]
      erw [MapStack.eq.StackMap]
      apply Eq.of.All_EqGetS.fin
      intro i
      erw [EqGetStack.fn.fin]
      simp
      erw [ih (X.get i)]
      rw [MaskedFill.eq.Stack_MaskedFillGet.of.GtLength_2.fin (by grind)]
      conv_rhs => erw [EqGetStack.fn.fin]
      congr 1
      conv_rhs => erw [GetMap.eq.MapGet.fin]
      rfl
    else if h_len_lt : (n :: s).length < 2 then
      simp [EqMaskedFill.of.LtLength_2 h_len_lt]
    else
      have h_s : s.length = 1 := by grind
      match s with
      | [m] =>
        repeat rw [Tensor.masked_fill, dif_neg h_len_gt, dif_neg h_len_lt]
        rw [MapStack.eq.StackMap]
        apply Eq.of.All_EqGetS.fin
        intro i
        repeat rw [EqGetStack.fn.fin]
        rw [MapStack.eq.StackMap]
        apply Eq.of.All_EqGetS.fin
        intro j
        repeat rw [EqGetStack.fn.fin]
        split_ifs with h
        · apply Eq.of.EqDataS
          dsimp [Tensor.map]
          simp [EqData0'0]
          ext i
          fin_cases i
          assumption
        · erw [GetMap.eq.MapGet.fin X f (i := ⟨i, by grind⟩)]
          erw [GetMap.eq.MapGet.fin (X.get i) f (i := ⟨j, by grind⟩)]
          rfl


-- created on 2026-07-29
