import Mathlib.Algebra.Ring.Defs
import Lemma.Fin.EqShiftRowShiftRow
import Lemma.Matrix.GetShiftMatrix.eq.DeltaShiftRow
import Lemma.Nat.Delta
import Lemma.Nat.Delta.eq.Ite
open Matrix Nat Fin


@[path]
private lemma main
  [AddMonoidWithOne α]
-- given
  (i₀ j₀ : Fin n) :
-- imply
  (shiftMatrix (α := α) i₀ j₀)ᵀ = shiftMatrix (α := α) j₀ i₀ := by
-- proof
  ext i j
  simp only [transpose_apply, GetShiftMatrix.eq.DeltaShiftRow]
  rw [Delta.comm]
  have hiff : i = j.shiftRow i₀ j₀ ↔ i.shiftRow j₀ i₀ = j := by
    constructor
    ·
      intro h
      rw [h, EqShiftRowShiftRow]
    ·
      intro h
      rw [← h, EqShiftRowShiftRow]
  simp only [Delta.eq.Ite]
  split_ifs with h h' h' <;> try rfl
  ·
    exact absurd (hiff.mp h) h'
  ·
    exact absurd (hiff.mpr h') h


-- created on 2026-11-01
