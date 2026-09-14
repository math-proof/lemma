import Lemma.Tensor.Delta.eq.Ite
import Lemma.Tensor.GetShiftMatrix.eq.DeltaShiftRow
import Lemma.Fin.ShiftRow.eq.Ite
import sympy.matrices.expressions.permutation
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetShiftMatrix.eq.Ite |
| fin | Tensor.GetShiftMatrix.eq.Ite.fin |
-/
@[main, fin]
private lemma main
  [AddMonoidWithOne α] [CharZero α]
  {n : ℕ}
-- given
  (i₀ j₀ i j : Fin n) :
-- imply
  (ShiftMatrix (α := α) i₀ j₀)[i, j] =
    if (i₀ : ℕ) = (j₀ : ℕ) then
      (↑(KroneckerDelta i j) : Tensor α [])
    else if (i₀ : ℕ) < (j₀ : ℕ) then
      if (i : ℕ) = (j₀ : ℕ) then
        (↑(KroneckerDelta (i₀ : ℕ) (j : ℕ)) : Tensor α [])
      else if (i₀ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (j₀ : ℕ) then
        (↑(KroneckerDelta ((i : ℕ) + 1) (j : ℕ)) : Tensor α [])
      else
        (↑(KroneckerDelta i j) : Tensor α [])
    else
      if (j : ℕ) = (i₀ : ℕ) then
        (↑(KroneckerDelta (i : ℕ) (j₀ : ℕ)) : Tensor α [])
      else if (j₀ : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i₀ : ℕ) then
        (↑(KroneckerDelta (i : ℕ) ((j : ℕ) + 1)) : Tensor α [])
      else
        (↑(KroneckerDelta i j) : Tensor α []) := by
-- proof
  rw [GetShiftMatrix.eq.DeltaShiftRow i₀ j₀ i j]
  simp only [Tensor.Delta.eq.Ite, Fin.ShiftRow.eq.Ite i i₀ j₀]
  split_ifs <;> first
  | rfl
  | omega


-- created on 2026-09-10
-- updated on 2026-09-13
