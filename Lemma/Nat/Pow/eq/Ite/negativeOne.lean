import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  -- imply
  : (-1 : ℤ) ^ n = if n % 2 = 0 then 1 else -1 := by
  -- proof
  have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h2 with (h2 | h2)
  · have he : ∃ k : ℕ, n = 2 * k := by
      refine ⟨n / 2, ?_⟩
      omega
    rcases he with ⟨k, hk⟩
    have hpow : (-1 : ℤ) ^ (2 * k) = 1 := by
      calc (-1 : ℤ) ^ (2 * k)
          = ((-1 : ℤ) ^ 2) ^ k := by rw [← pow_mul]
        _ = (1 : ℤ) ^ k := by norm_num
        _ = (1 : ℤ) := by simp
    have hif : (if (2 * k) % 2 = 0 then (1 : ℤ) else (-1 : ℤ)) = 1 := by
      simp
    rw [hk, hpow, hif]
  · have ho : ∃ k : ℕ, n = 2 * k + 1 := by
      refine ⟨n / 2, ?_⟩
      omega
    rcases ho with ⟨k, hk⟩
    have hpow : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
      calc (-1 : ℤ) ^ (2 * k + 1)
          = (-1 : ℤ) ^ (2 * k) * (-1 : ℤ) := by rw [pow_add, pow_one]
        _ = ((-1 : ℤ) ^ 2) ^ k * (-1 : ℤ) := by rw [← pow_mul]
        _ = (1 : ℤ) * (-1 : ℤ) := by norm_num
        _ = (-1 : ℤ) := by ring
    have hif : (if (2 * k + 1) % 2 = 0 then (1 : ℤ) else (-1 : ℤ)) = -1 := by
      simp [Nat.add_mod]
    rw [hk, hpow, hif]

-- created on 2020-03-01
