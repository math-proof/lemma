import Lemma.Nat.Delta
import Lemma.Tensor.EqGetT
import Lemma.Tensor.GetShiftMatrix.eq.Ite
open Nat Tensor
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [AddMonoidWithOne α] [CharZero α]
  (n i₀ j₀ : ℕ) :
-- imply
  (ShiftMatrix (α := α) n i₀ j₀)ᵀ = ShiftMatrix n j₀ i₀ := by
-- proof
  let P := ShiftMatrix (α := α) n i₀ j₀
  let Q := ShiftMatrix (α := α) n j₀ i₀
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply (EqGetT P j i).trans
  have hL := GetShiftMatrix.eq.Ite (α := α) n i₀ j₀ j i
  have hR := GetShiftMatrix.eq.Ite (α := α) n j₀ i₀ i j
  simp only [GetElem.getElem] at hL hR ⊢
  rw [hL]
  erw [hR]
  by_cases h : i₀ = j₀
  ·
    subst h
    split_ifs
    .
      rw [Delta.comm]
    repeat grind
  ·
    split_ifs
    repeat grind
    .
      rw [Delta.comm]
    repeat grind
    .
      rw [Delta.comm]
    repeat grind
    .
      rw [Delta.comm]
    .
      grind
    .
      rw [Delta.comm]
    repeat grind
    .
      rw [Delta.comm]
    repeat grind
    .
      rw [Delta.comm]
    repeat grind


-- created on 2026-09-10
