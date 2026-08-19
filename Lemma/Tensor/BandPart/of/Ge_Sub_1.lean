import Lemma.Tensor.BandPart.eq.Stack_BoolIn_Icc
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma main
  [AddMonoidWithOne α]
  {n m l u : ℕ}
-- given
  (h : l ≥ n - 1) :
-- imply
  (1 : Tensor α [n, m]).band_part l u = (1 : Tensor α [n, m]).band_part (n - 1) u := by
-- proof
  rw [BandPart.eq.Stack_BoolIn_Icc, BandPart.eq.Stack_BoolIn_Icc]
  apply Eq.of.All_EqGetS.fin
  intro i
  simp only [EqGetStack.fin]
  apply Eq.of.All_EqGetS.fin
  intro j
  simp only [EqGetStack.fin]
  have hji : (j - i : ℤ) ≥ -((n - 1 : ℕ) : ℤ) := by
    have : (i : ℤ) ≤ ↑(n - 1) := by
      simp [Nat.cast_le]
      exact Nat.le_pred_of_lt i.isLt
    have : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
    linarith
  have hl : (-(l : ℤ)) ≤ -((n - 1 : ℕ) : ℤ) := neg_le_neg (Nat.cast_le.mpr h)
  have h_iff : ((j - i : ℤ) ∈ Icc (-(l : ℤ)) u) ↔ ((j - i : ℤ) ∈ Icc (-((n - 1 : ℕ) : ℤ)) u) := by
    constructor
    ·
      intro h
      exact ⟨hji, h.2⟩
    ·
      intro h
      exact ⟨le_trans hl hji, h.2⟩
  simp [h_iff]


-- created on 2026-08-16
