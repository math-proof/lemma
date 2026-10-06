import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {n : ℤ}
  -- given
  (h : n % 2 ≠ 0)
  -- imply
  : ∃ k : ℤ, n = 2 * k + 1 := by
  -- proof
  have hnonneg : 0 ≤ n % 2 := Int.emod_nonneg n (by norm_num)
  have hlt : n % 2 < 2 := Int.emod_lt_of_pos n (by norm_num)
  have h1 : n % 2 = 1 := by omega
  have hdiv : n = n % 2 + 2 * (n / 2) := by
    linarith [Int.emod_add_mul_ediv n 2]
  refine ⟨n / 2, ?_⟩
  linarith

-- created on 2023-05-26
