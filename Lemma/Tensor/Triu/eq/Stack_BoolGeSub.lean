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
  (1 : Tensor α [n, n]).triu d = [i < n] [j < n] ((j - i : ℤ) ≥ d : Bool) := by
-- proof
  unfold Tensor.triu
  simp [Tensor.masked_fill]
  apply Eq.of.All_EqGetS.fin
  intro i
  repeat rw [EqGetStack.fn.fin]
  apply Eq.of.All_EqGetS.fin
  intro j
  repeat rw [EqGetStack.fn.fin]
  split_ifs with h_u
  ·
    have h_u : ¬d ≤ j - i := by
      linarith
    simp [h_u]
  ·
    simp at h_u
    simp [h_u]
    repeat rw [EqGet1_1.fin]


-- created on 2026-01-03
