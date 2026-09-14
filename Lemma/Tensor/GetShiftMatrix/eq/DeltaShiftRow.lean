import Lemma.Tensor.EqGetStack
import sympy.matrices.expressions.permutation
open Tensor


/--
Entry of `ShiftMatrix i₀ j₀`: row `i` is sent to `i.shiftRow i₀ j₀`.
-/
@[main]
private lemma main
  [AddMonoidWithOne α] [CharZero α]
  {n : ℕ}
-- given
  (i₀ j₀ i j : Fin n) :
-- imply
  (ShiftMatrix (α := α) i₀ j₀)[i, j] =
    (↑(KroneckerDelta (i.shiftRow i₀ j₀ : ℕ) (j : ℕ)) : Tensor α []) := by
-- proof
  simp only [ShiftMatrix]
  have hrow := EqGetStack.fin
    (fun i : Fin n => [j < n] (↑(KroneckerDelta (i.shiftRow i₀ j₀) j) : Tensor α [])) i
  have hcol := EqGetStack.fin
    (fun j : Fin n => (↑(KroneckerDelta (i.shiftRow i₀ j₀) j) : Tensor α [])) j
  simp [GetElem.getElem] at hrow hcol ⊢
  erw [hrow, hcol]
  simp [KroneckerDelta, Fin.ext_iff]


-- created on 2026-09-13
