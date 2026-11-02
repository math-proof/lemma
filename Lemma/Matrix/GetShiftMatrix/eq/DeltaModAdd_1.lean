import Mathlib.Algebra.Ring.Defs
import Lemma.Matrix.GetShiftMatrix.eq.Ite
import Lemma.Nat.Delta.eq.Ite
open Matrix Nat


@[path]
private lemma main
  [AddMonoidWithOne α]
-- given
  (n : ℕ)
  (i j : Fin n) :
-- imply
  (shiftMatrix (α := α) ⟨0, i.size_positive⟩ ⟨n - 1, by have := i.size_positive; omega⟩) i j =
    (KroneckerDelta (((i : ℕ) + 1) % n) (j : ℕ) : α) := by
-- proof
  have hn : 0 < n := i.size_positive
  have h := GetShiftMatrix.eq.Ite (α := α) ⟨0, hn⟩ ⟨n - 1, by omega⟩ i j
  rw [h]
  if h1 : n = 1 then
    subst h1
    have hi : (i : Fin 1) = 0 := Fin.fin_one_eq_zero i
    have hj : (j : Fin 1) = 0 := Fin.fin_one_eq_zero j
    subst hi
    subst hj
    simp only [Delta.eq.Ite]
    simp
  else
    have h2 : 1 < n := by omega
    rw [ite_eq_right (by omega : ¬ ((0 : ℕ) = n - 1)), ite_eq_left (by omega : (0 : ℕ) < n - 1)]
    if hi_last : (i : ℕ) = n - 1 then
      rw [ite_eq_left hi_last]
      congr 1
      have hie : (i : ℕ) + 1 = n := by omega
      rw [hie, Nat.mod_self]
    else
      have hmid : (0 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < n - 1 := by
        simp
        omega
      rw [ite_eq_right hi_last, ite_eq_left hmid]
      rw [Nat.mod_eq_of_lt (by omega : (i : ℕ) + 1 < n)]


-- created on 2026-11-01
