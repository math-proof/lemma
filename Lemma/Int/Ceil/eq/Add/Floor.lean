import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n d : ℤ}
-- given
  (hd : d ≠ 0) :
-- imply
  ⌈(n : ℝ) / d⌉ = ⌊((n - Int.sign d : ℤ) : ℝ) / d⌋ + 1 := by
-- proof
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  rcases lt_or_gt_of_ne hd with h | h
  · have hdr : (d : ℝ) < 0 := by exact_mod_cast h
    rw [Int.sign_eq_neg_one_of_neg h]
    have h1 := Int.floor_le (((n - -1 : ℤ) : ℝ) / d)
    have h2 := Int.lt_floor_add_one (((n - -1 : ℤ) : ℝ) / d)
    generalize ⌊((n - -1 : ℤ) : ℝ) / d⌋ = q at h1 h2 ⊢
    rw [le_div_iff_of_neg hdr] at h1
    rw [div_lt_iff_of_neg hdr] at h2
    have i1 : n - -1 ≤ q * d := by exact_mod_cast h1
    have i2 : (q + 1) * d < n - -1 := by exact_mod_cast h2
    have g1 : (q : ℝ) < n / d := by
      rw [lt_div_iff_of_neg hdr]
      exact_mod_cast (by linarith : n < q * d)
    have g2 : (n : ℝ) / d ≤ q + 1 := by
      rw [div_le_iff_of_neg hdr]
      exact_mod_cast (by linarith : (q + 1) * d ≤ n)
    rw [Int.ceil_eq_iff]
    push_cast
    constructor <;> linarith
  · have hdr : (0 : ℝ) < d := by exact_mod_cast h
    rw [Int.sign_eq_one_of_pos h]
    have h1 := Int.floor_le (((n - 1 : ℤ) : ℝ) / d)
    have h2 := Int.lt_floor_add_one (((n - 1 : ℤ) : ℝ) / d)
    generalize ⌊((n - 1 : ℤ) : ℝ) / d⌋ = q at h1 h2 ⊢
    rw [le_div_iff₀ hdr] at h1
    rw [div_lt_iff₀ hdr] at h2
    have i1 : q * d ≤ n - 1 := by exact_mod_cast h1
    have i2 : n - 1 < (q + 1) * d := by exact_mod_cast h2
    have g1 : (q : ℝ) < n / d := by
      rw [lt_div_iff₀ hdr]
      exact_mod_cast (by linarith : q * d < n)
    have g2 : (n : ℝ) / d ≤ q + 1 := by
      rw [div_le_iff₀ hdr]
      exact_mod_cast (by linarith : n ≤ (q + 1) * d)
    rw [Int.ceil_eq_iff]
    push_cast
    constructor <;> linarith


-- created on 2026-09-27
