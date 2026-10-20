import Mathlib.Algebra.BigOperators.Intervals
import sympy.Basic
open Finset


/--
Conditional expectation of a fair die on `{1, …, n}` given that the face is strictly above `n / 2`.
The surviving faces are `⌊n/2⌋ + 1, …, n`, and their average is `(n + 1) / 2 + ⌊n/2⌋ / 2`.
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (h₀ : 0 < n) :
-- imply
  (∑ k ∈ Icc (n / 2 + 1) n, (k : ℚ)) / ((n - n / 2 : ℕ) : ℚ) =
    ((n + 1 : ℕ) : ℚ) / 2 + ((n / 2 : ℕ) : ℚ) / 2 := by
-- proof
  have ha : n / 2 + 1 ≤ n := by omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le ha
  have sum_Icc_two : ∀ a t, 2 * ∑ k ∈ Icc a (a + t), k = (t + 1) * (2 * a + t) := by
    intro a t
    induction t with
    | zero => simp [Icc_self]
    | succ t ih =>
      have hnot : a + t + 1 ∉ Icc a (a + t) := by simp [mem_Icc]
      have hins : Icc a (a + (t + 1)) = insert (a + t + 1) (Icc a (a + t)) := by
        ext k
        simp only [mem_insert, mem_Icc]
        omega
      rw [hins, sum_insert hnot, mul_add, ih]
      ring
  have hsum : 2 * ∑ k ∈ Icc (n / 2 + 1) n, k = (t + 1) * (2 * (n / 2 + 1) + t) := by
    have h := sum_Icc_two (n / 2 + 1) t
    rwa [← ht] at h
  have ht' : t + 1 = n - n / 2 := by omega
  have hab : 2 * (n / 2 + 1) + t = n / 2 + 1 + n := by omega
  have hsumQ : ∑ k ∈ Icc (n / 2 + 1) n, (k : ℚ) =
      ((n - n / 2 : ℕ) : ℚ) * ((n / 2 + 1 + n : ℕ) : ℚ) / 2 := by
    have h := congrArg (fun m : ℕ => (m : ℚ)) hsum
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h
    rw [show (t : ℚ) + (1 : ℕ) = ((t + 1 : ℕ) : ℚ) by norm_cast, ht'] at h
    rw [show (2 : ℚ) * (((n / 2 : ℕ) : ℚ) + (1 : ℕ)) + (t : ℚ) =
        ((n / 2 + 1 + n : ℕ) : ℚ) by exact_mod_cast hab] at h
    exact (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).2 (by simpa [mul_comm] using h)
  have hne : ((n - n / 2 : ℕ) : ℚ) ≠ 0 := by
    have : 0 < n - n / 2 := by omega
    exact_mod_cast this.ne'
  rw [hsumQ, div_div]
  field_simp [hne]
  norm_cast
  omega


-- created on 2021-08-06
-- updated on 2026-10-17
