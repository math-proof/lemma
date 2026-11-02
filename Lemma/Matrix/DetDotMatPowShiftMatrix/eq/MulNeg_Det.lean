import Lemma.Matrix.DetDotMatPowShiftMatrix.eq.Mul_Det
open Matrix Finset


@[path]
private lemma main
  [CommRing α]
-- given
  (A : Matrix (Fin 6) (Fin 6) α) :
-- imply
  (∑ k ∈ Finset.Ico 1 6,
      (shiftMatrix (α := α) (0 : Fin 6) 5 ^ k) * A).det =
    -5 * A.det := by
-- proof
  have hn : 0 < 6 := by decide
  have h := DetDotMatPowShiftMatrix.eq.Mul_Det (α := α) hn A
  have h0 : (⟨0, hn⟩ : Fin 6) = 0 := by
    apply Fin.ext
    rfl
  have h5 : (⟨6 - 1, by omega⟩ : Fin 6) = 5 := by
    apply Fin.ext
    rfl
  simp [h0, h5] at h
  have hc : (-1 : α) ^ 5 * 5 = -5 := by
    have hpow : (-1 : α) ^ 5 = -1 := Odd.neg_one_pow ⟨2, rfl⟩
    rw [hpow]
    simp
  rw [hc] at h
  apply h


-- created on 2020-10-03
-- updated on 2026-11-01
