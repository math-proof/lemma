import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {a b : ℕ → ℂ}
-- given
  (h : ∀ i, b i ≠ 0) :
-- imply
  (Matrix.of fun i j : Fin (n + 1) => a (min (i : ℕ) j) * b (max (i : ℕ) j)).det =
    a 0 * b n * ∏ i ∈ Finset.range n, (a (i + 1) * b i - a i * b (i + 1)) := by
-- proof
  induction n with
  | zero =>
    simp [Matrix.det_unique]
  | succ n ih =>
    set M := Matrix.of fun i j : Fin (n + 2) => a (min (i : ℕ) j) * b (max (i : ℕ) j) with hM
    have hne : Fin.last (n + 1) ≠ (Fin.last n).castSucc := by
      intro e
      have := congrArg Fin.val e
      simp at this
    have hb := h n
    rw [← Matrix.det_updateRow_add_smul_self M hne (-(b (n + 1) / b n)), Matrix.det_succ_row _ (Fin.last (n + 1)),
      Fin.sum_univ_castSucc]
    have hz : ∀ j : Fin (n + 1), (M.updateRow (Fin.last (n + 1)) (M (Fin.last (n + 1)) +
        (-(b (n + 1) / b n)) • M (Fin.last n).castSucc)) (Fin.last (n + 1)) j.castSucc = 0 := by
      intro j
      have hj := j.isLt
      simp only [Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hM, Matrix.of_apply, Fin.val_last,
        Fin.val_castSucc]
      rw [min_eq_right (by omega), max_eq_left (by omega), min_eq_right (by omega), max_eq_left (by omega)]
      field_simp
      ring
    have hsub : (M.updateRow (Fin.last (n + 1)) (M (Fin.last (n + 1)) + (-(b (n + 1) / b n)) • M (Fin.last n).castSucc)).submatrix
        (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove =
        Matrix.of fun i j : Fin (n + 1) => a (min (i : ℕ) j) * b (max (i : ℕ) j) := by
      ext i j
      rw [Fin.succAbove_last, Matrix.submatrix_apply, Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
      simp [hM]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rw [hsub, ih, Finset.prod_range_succ]
    simp only [Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hM, Matrix.of_apply, Fin.val_last,
      Fin.val_castSucc, min_self, max_self]
    rw [min_eq_left (by omega), max_eq_right (by omega), ← two_mul, pow_mul]
    field_simp
    ring


-- created on 2020-10-15
