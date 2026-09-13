import Lemma.Tensor.Delta.eq.Ite
import Lemma.Tensor.GetShiftMatrix.eq.Ite
import Lemma.Fin.ShiftRow.eq.Ite
import sympy.matrices.expressions.permutation
open Tensor


/--
Entry of `ShiftMatrix(n, i₀, j₀)`: row `i` is sent to `i.shiftRow i₀ j₀`.
-/
@[main]
private lemma main
-- given
  (n : ℕ)
  (i₀ j₀ : Fin n)
  (i j : Fin n) :
-- imply
  (ShiftMatrix (α := ℝ) n (i₀ : ℕ) (j₀ : ℕ))[i, j] =
    (↑(KroneckerDelta (i.shiftRow i₀ j₀ : ℕ) (j : ℕ)) : Tensor ℝ []) := by
-- proof
  have hS := GetShiftMatrix.eq.Ite (α := ℝ) n (i₀ : ℕ) (j₀ : ℕ) i₀.isLt j₀.isLt i j
  rw [hS]
  have hδij : KroneckerDelta i j = KroneckerDelta (i : ℕ) (j : ℕ) := by
    simp [KroneckerDelta, Fin.ext_iff]
  rw [hδij]
  simp only [Delta.eq.Ite, Fin.ShiftRow.eq.Ite i i₀ j₀]
  split_ifs <;> first | rfl | omega


-- created on 2026-09-13
