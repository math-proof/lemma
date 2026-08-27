import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.EqGetStack
import sympy.matrices.expressions.special
open Tensor


@[main]
private lemma main
  [AddMonoidWithOne α]
-- given
  (m n l u d : ℕ) :
-- imply
  (1 : Tensor α [m, n]).band_part l u d = [i < m] [j < n] (((j - i : ℤ) ∈ Icc (-l : ℤ) u ∧ (d : ℤ) ∣ (j - i : ℤ) + l) : Bool) := by
-- proof
  unfold Tensor.band_part Tensor.triu Tensor.tril
  simp [Tensor.masked_fill]
  apply Eq.of.All_EqGetS.fin
  intro i
  simp [EqGetStack.fin]
  erw [EqGetStack.fin]
  erw [EqGetStack.fin]
  apply Eq.of.All_EqGetS.fin
  intro j
  simp [EqGetStack.fin]
  erw [EqGetStack.fin]
  conv_lhs => simp [EqGetStack.fin]
  conv_lhs =>
    arg 2
    arg 3
    erw [EqGetStack.fin]
  split_ifs with h_dvd h_triu h_tril
  ·
    have h1 : ¬((i : ℤ) ≤ j + l) := by linarith
    simp [h1]
  ·
    have h2 : ¬((j : ℤ) ≤ u + i) := by linarith
    simp [h2]
    grind
  ·
    rw [EqGet1_1.fin]
    erw [EqGet1_1.fin]
    have h1 : (i : ℤ) ≤ j + l := by linarith
    have h2 : (j : ℤ) ≤ u + i := by linarith
    simp [h_dvd, h1, h2]
    grind
  ·
    simp [decide_eq_false_iff_not.mpr h_dvd]


-- created on 2026-07-28
