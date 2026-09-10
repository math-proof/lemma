import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.GetShiftMatrix.eq.Ite
open Nat Tensor


@[main, fin]
private lemma main
  [AddMonoidWithOne α] [CharZero α]
  (n : ℕ) (h : 0 < n)
  (i j : Fin n) :
-- imply
  (ShiftMatrix (α := α) n 0 (n - 1))[i, j] =
    (↑(KroneckerDelta (((i : ℕ) + 1) % n) (j : ℕ)) : Tensor α []) := by
-- proof
  have h := GetShiftMatrix.eq.Ite (α := α) n 0 (n - 1) i j
  simp only [GetElem.getElem] at h ⊢
  rw [h]
  by_cases h1 : n = 1
  ·
    subst h1
    have hi : (i : Fin 1) = 0 := Fin.fin_one_eq_zero i
    have hj : (j : Fin 1) = 0 := Fin.fin_one_eq_zero j
    subst hi
    subst hj
    simp only [Delta.eq.Ite]
    simp
  ·
    have h2 : 1 < n := by omega
    rw [if_neg (by omega : ¬ ((0 : ℕ) = n - 1)), if_pos (by omega : (0 : ℕ) < n - 1)]
    by_cases hi_last : (i : ℕ) = n - 1
    ·
      rw [if_pos hi_last]
      congr 1
      have hie : (i : ℕ) + 1 = n := by omega
      rw [hie, Nat.mod_self]
    ·
      rw [if_neg hi_last, if_pos (by simp; omega : (0 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < n - 1)]
      rw [Nat.mod_eq_of_lt (by omega : (i : ℕ) + 1 < n)]


-- created on 2026-09-11
