import Lemma.Tensor.Stack.eq.AppendStackS
import Lemma.Algebra.Eq_0
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqSliceS.Eq.of.Eq
open Tensor Algebra


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
    let ⟨h_slice, h_n⟩ := Tensor.EqSliceS.Eq.of.Eq h
    constructor
    ·
      simp at h_slice
      sorry
    ·
      simp at h_n
      sorry
  ·
    intro ⟨h₀, h₁⟩
    calc
      [i < n + 1] f i = [i < n] f i ++ [i < 1] f (n + i) := Stack.eq.AppendStackS f
      _ = [i < n] g i ++ [i < 1] g (n + i) := by
        rw [h₀]
        have : [i < 1] f (n + i) = [i < 1] g (n + i) := by
          apply Eq.of.All_EqGetS
          intro i
          rw [Eq_0 i]
          simp [GetElem.getElem]
          repeat rw [EqGetStack.fin.fin]
          simp
          assumption
        rw [this]
      _ = [i < n + 1] g i := (Stack.eq.AppendStackS g).symm


-- created on 2024-07-01
-- updated on 2025-06-14
