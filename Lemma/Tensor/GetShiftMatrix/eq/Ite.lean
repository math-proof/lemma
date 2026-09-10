import Lemma.Tensor.EqGetStack
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
  (n i₀ j₀ : ℕ)
  (i j : Fin n) :
-- imply
  (ShiftMatrix (α := α) n i₀ j₀)[i, j] =
    if i₀ = j₀ then
      (↑(KroneckerDelta i j) : Tensor α [])
    else if i₀ < j₀ then
      if (i : ℕ) = j₀ then
        (↑(KroneckerDelta i₀ (j : ℕ)) : Tensor α [])
      else if i₀ ≤ (i : ℕ) ∧ (i : ℕ) < j₀ then
        (↑(KroneckerDelta ((i : ℕ) + 1) (j : ℕ)) : Tensor α [])
      else
        (↑(KroneckerDelta i j) : Tensor α [])
    else
      if (j : ℕ) = i₀ then
        (↑(KroneckerDelta (i : ℕ) j₀) : Tensor α [])
      else if j₀ ≤ (j : ℕ) ∧ (j : ℕ) < i₀ then
        (↑(KroneckerDelta (i : ℕ) ((j : ℕ) + 1)) : Tensor α [])
      else
        (↑(KroneckerDelta i j) : Tensor α []) := by
-- proof
  simp [ShiftMatrix]
  have hrow :=
    EqGetStack.fin
      (fun i : Fin n =>
        [j < n]
          (if i₀ = j₀ then
            (↑(KroneckerDelta i j) : Tensor α [])
          else if i₀ < j₀ then
            if (i : ℕ) = j₀ then
              (↑(KroneckerDelta i₀ (j : ℕ)) : Tensor α [])
            else if i₀ ≤ (i : ℕ) ∧ (i : ℕ) < j₀ then
              (↑(KroneckerDelta ((i : ℕ) + 1) (j : ℕ)) : Tensor α [])
            else
              (↑(KroneckerDelta i j) : Tensor α [])
          else
            if (j : ℕ) = i₀ then
              (↑(KroneckerDelta (i : ℕ) j₀) : Tensor α [])
            else if j₀ ≤ (j : ℕ) ∧ (j : ℕ) < i₀ then
              (↑(KroneckerDelta (i : ℕ) ((j : ℕ) + 1)) : Tensor α [])
            else
              (↑(KroneckerDelta i j) : Tensor α [])))
      i
  have hcol :=
    EqGetStack.fin
      (fun j : Fin n =>
        if i₀ = j₀ then
          (↑(KroneckerDelta i j) : Tensor α [])
        else if i₀ < j₀ then
          if (i : ℕ) = j₀ then
            (↑(KroneckerDelta i₀ (j : ℕ)) : Tensor α [])
          else if i₀ ≤ (i : ℕ) ∧ (i : ℕ) < j₀ then
            (↑(KroneckerDelta ((i : ℕ) + 1) (j : ℕ)) : Tensor α [])
          else
            (↑(KroneckerDelta i j) : Tensor α [])
        else
          if (j : ℕ) = i₀ then
            (↑(KroneckerDelta (i : ℕ) j₀) : Tensor α [])
          else if j₀ ≤ (j : ℕ) ∧ (j : ℕ) < i₀ then
            (↑(KroneckerDelta (i : ℕ) ((j : ℕ) + 1)) : Tensor α [])
          else
            (↑(KroneckerDelta i j) : Tensor α []))
      j
  simp [GetElem.getElem] at hrow hcol ⊢
  erw [hrow, hcol]


-- created on 2026-09-10
