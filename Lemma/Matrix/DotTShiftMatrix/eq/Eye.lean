import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Defs
import Lemma.Fin.EqShiftRowShiftRow
import Lemma.Matrix.GetShiftMatrix.eq.DeltaShiftRow
import Lemma.Nat.Delta.eq.Ite
open Matrix Nat Fin


@[path]
private lemma main
  [Semiring α]
-- given
  (i₀ j₀ : Fin n) :
-- imply
  (shiftMatrix (α := α) j₀ i₀) * (shiftMatrix (α := α) i₀ j₀) =
    (1 : Matrix (Fin n) (Fin n) α) := by
-- proof
  ext i j
  simp only [mul_apply, one_apply, GetShiftMatrix.eq.DeltaShiftRow]
  have hsum :
    (∑ k : Fin n,
        (KroneckerDelta (i.shiftRow j₀ i₀) k : α) *
          (KroneckerDelta (k.shiftRow i₀ j₀) j : α)) =
      (KroneckerDelta ((i.shiftRow j₀ i₀).shiftRow i₀ j₀) j : α) := by
    refine Eq.trans (Finset.sum_eq_single (i.shiftRow j₀ i₀) ?_ ?_) ?_
    ·
      intro k _ hk
      have hk' : i.shiftRow j₀ i₀ ≠ k := Ne.symm hk
      simp [Delta.eq.Ite, hk']
    ·
      intro hmem
      exact (hmem (Finset.mem_univ _)).elim
    ·
      simp [Delta.eq.Ite]
  rw [hsum, EqShiftRowShiftRow]
  simp [Delta.eq.Ite]


-- created on 2026-11-01
