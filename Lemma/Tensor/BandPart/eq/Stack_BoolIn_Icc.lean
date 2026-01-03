import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.EqGetStack
import sympy.matrices.expressions.special
open Tensor


@[main]
private lemma main
  [AddMonoidWithOne α]
-- given
  (n l u : ℕ) :
-- imply
  (1 : Tensor α [n, n]).band_part l u = [i < n] [j < n] (((j - i : ℤ) ∈ Icc (-l : ℤ) u) : Bool) := by
-- proof
  unfold Tensor.band_part Tensor.triu Tensor.tril
  simp [Tensor.masked_fill]
  apply Eq.of.All_EqGetS.fin
  intro i
  repeat rw [EqGetStack.fn.fin]
  apply Eq.of.All_EqGetS.fin
  intro j
  repeat rw [EqGetStack.fn.fin]
  split_ifs with h_l h_u
  ·
    have h_l : ¬(i : ℤ) ≤ j + l := by
      linarith
    simp [h_l]
  ·
    simp at h_l
    simp [h_l]
    have h_u : ¬(j : ℤ) ≤ u + i := by
      linarith
    simp [h_u]
  ·
    repeat rw [EqGet1_1.fin]
    simp at h_l
    simp at h_u
    simp [h_l, h_u]


-- created on 2026-01-02
-- updated on 2026-01-03
