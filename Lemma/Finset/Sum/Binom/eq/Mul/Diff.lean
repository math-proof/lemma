import Mathlib.Algebra.Group.ForwardDiff
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {i j : ℤ}
  (f : ℤ → ℝ) :
-- imply
  ∑ k ∈ Finset.Ico i (n + i + 1), (-1 : ℝ) ^ (j - k) * ((n.choose (k - i).toNat : ℕ) : ℝ) * f k =
    (-1 : ℝ) ^ ((n : ℤ) + i - j) * (fwdDiff 1)^[n] f i := by
-- proof
  have hsign : ∀ a t : ℤ, (-1 : ℝ) ^ (a + 2 * t) = (-1) ^ a := fun a t => by
    rw [zpow_add₀ (by norm_num), zpow_mul]
    norm_num
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  refine Finset.sum_nbij' (fun k => (k - i).toNat) (fun m => i + m) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
    omega
  · intro m hm
    simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢
    omega
  · intro k hk
    simp only [Finset.mem_Ico] at hk
    omega
  · intro m _
    simp
  · intro k hk
    simp only [Finset.mem_Ico] at hk
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = i + m := ⟨(k - i).toNat, by omega⟩
    have hm : m ≤ n := by omega
    simp only [add_sub_cancel_left, Int.toNat_natCast, nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [← zpow_natCast, Nat.cast_sub hm, ← mul_assoc, ← mul_assoc, ← zpow_add₀ (by norm_num),
      show (n : ℤ) + i - j + ((n : ℤ) - m) = j - (i + m) + 2 * (n + i - j) by ring, hsign]


-- created on 2021-11-26
