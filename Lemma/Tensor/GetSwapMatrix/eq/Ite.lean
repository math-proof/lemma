import Lemma.Tensor.EqGetStack
import sympy.matrices.expressions.permutation
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetSwapMatrix.eq.Ite |
| fin | Tensor.GetSwapMatrix.eq.Ite.fin |
-/
@[main, fin]
private lemma main
  [AddMonoidWithOne α] [CharZero α]
-- given
  (i₀ j₀ : ℕ)
  (i j : Fin n) :
-- imply
  (SwapMatrix (α := α) n i₀ j₀)[i, j] =
    if (i : ℕ) = j₀ then
      (↑(KroneckerDelta (j : ℕ) i₀) : Tensor α [])
    else if (i : ℕ) = i₀ then
      (↑(KroneckerDelta (j : ℕ) j₀) : Tensor α [])
    else
      (↑(KroneckerDelta j i) : Tensor α []) := by
-- proof
  simp [SwapMatrix]
  have hrow :=
    EqGetStack.fin
      (fun i : Fin n =>
        [j < n]
          (if (i : ℕ) = j₀ then
            (↑(KroneckerDelta (j : ℕ) i₀) : Tensor α [])
          else if (i : ℕ) = i₀ then
            (↑(KroneckerDelta (j : ℕ) j₀) : Tensor α [])
          else
            (↑(KroneckerDelta j i) : Tensor α [])))
      i
  have hcol :=
    EqGetStack.fin
      (fun j : Fin n =>
        if (i : ℕ) = j₀ then
          (↑(KroneckerDelta (j : ℕ) i₀) : Tensor α [])
        else if (i : ℕ) = i₀ then
          (↑(KroneckerDelta (j : ℕ) j₀) : Tensor α [])
        else
          (↑(KroneckerDelta j i) : Tensor α []))
      j
  simp [GetElem.getElem] at hrow hcol ⊢
  erw [hrow, hcol]


-- created on 2020-07-25
-- updated on 2026-09-08
