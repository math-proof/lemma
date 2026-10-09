import Mathlib
import sympy.Basic


/--
[Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul.lean)
-/

private lemma  exists_shift (t n : ℤ) (htn : t ^ 2 < 4 * n) :
    ∃ k : ℤ, 0 < k * k - t * k + n ∧ ¬ IsSquare (k * k - t * k + n) ∧ (t - 2 * k) ^ 2 < 4 * (k * k - t * k + n) := by
  set D : ℤ := 4 * n - t ^ 2 with hD
  have hD0 : 0 < D := by omega
  refine ⟨D + |t|, ?_, ?_, ?_⟩
  · nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (2 * (D + |t|) - t)]
  · rintro ⟨s, hs⟩
    set m : ℤ := 2 * (D + |t|) - t with hm
    have hmD : D < m := by
      have := abs_nonneg t; have := le_abs_self t; have := neg_abs_le t; omega
    have h4 : 4 * (s * s) = m * m + D := by rw [← hs, hm, hD]; ring
    rcases le_or_gt (2 * |s|) m with h | h
    · nlinarith [sq_abs s, abs_nonneg s]
    · nlinarith [sq_abs s, abs_nonneg s]
  · nlinarith [abs_nonneg t, sq_abs t]
@[path]
private lemma main
  {t n : ℤ}
-- given
  (htn : t ^ 2 < 4 * n) :
-- imply
  ∃ k : ℤ, 0 < k ^ 2 - t * k + n ∧ ¬ IsSquare (k ^ 2 - t * k + n) := by
-- proof
  obtain ⟨k, h1, h2, -⟩ := exists_shift t n htn
  exact ⟨k, by rw [sq]; exact h1, by rw [sq]; exact h2⟩


-- created on 2026-10-05
