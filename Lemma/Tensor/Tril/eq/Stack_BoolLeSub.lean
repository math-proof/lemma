import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.EqGetStack
import sympy.matrices.expressions.special
open Tensor


@[main]
private lemma main
  [AddMonoidWithOne α]
-- given
  (n : ℕ)
  (d : ℤ) :
-- imply
  (1 : Tensor α [n, n]).tril d = [i < n] [j < n] ((j - i : ℤ) ≤ d : Bool) := by
-- proof
  unfold Tensor.tril
  simp [Tensor.masked_fill]
  apply Eq.of.All_EqGetS.fin
  intro i
  repeat rw [EqGetStack.fn.fin]
  apply Eq.of.All_EqGetS.fin
  intro j
  repeat rw [EqGetStack.fn.fin]
  split_ifs with h_l
  ·
    have h_l : ¬(j : ℤ) ≤ d + i := by 
      linarith
    simp [h_l]
  ·
    simp at h_l
    simp [h_l]
    repeat rw [EqGet1_1.fin]


-- created on 2026-01-03
