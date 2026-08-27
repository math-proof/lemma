import Lemma.Tensor.Stack.eq.AppendStackS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Slice.Eq.of.Eq
import Lemma.Tensor.GetSliceStack.as.Stack_UFn
import Lemma.Bool.SEq.is.Eq
open Tensor Bool


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Stack.is.Stack.Eq |
| comm | Tensor.EqStackS.Eq.is.EqStackS |
| mp | Tensor.EqStackS.Eq.of.EqStackS |
| mpr | Tensor.EqStackS.of.EqStackS.Eq |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (n : ℕ)
  (f g : ℕ → Tensor α s) :
-- imply
  [i < n + 1] f i = [i < n + 1] g i ↔ [i < n] f i = [i < n] g i ∧ f n = g n := by
-- proof
  constructor
  ·
    intro h
    let ⟨h_slice, h_n⟩ := Tensor.Slice.Eq.of.Eq h
    constructor
    ·
      apply Eq.of.SEq
      have h_f := GetSliceStack.as.Stack_UFn f n 1
      rw [h_slice] at h_f
      apply h_f.symm.trans
      apply GetSliceStack.as.Stack_UFn g n 1
    ·
      simp only [GetElem.getElem] at h_n
      repeat erw [EqGetStack.fun.fin] at h_n
      assumption
  ·
    intro ⟨h₀, h₁⟩
    calc
      _ = [i < n] f i ++ [i < 1] f (n + i) := Stack.eq.AppendStackS f
      _ = [i < n] g i ++ [i < 1] g (n + i) := by
        rw [h₀]
        congr 1
        apply Eq.of.All_EqGetS
        intro i
        fin_cases i
        repeat rw [EqGetStack]
        simpa
      _ = [i < n + 1] g i := (Stack.eq.AppendStackS g).symm


-- created on 2019-05-01
-- updated on 2025-06-14
