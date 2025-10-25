import Lemma.Real.Sqrt.eq.Root_2
open Real


@[main]
private lemma main
  {x : ℝ}
  {i : ℕ}
-- given
  (h₀ : x > 1)
  (h₁ : i > 0) :
-- imply
  x ^ (1 / (i + 2) : ℝ) < √x := by
-- proof
  -- We need to show that x^(1/(i+2)) ≤ x^(1/2) for x ≥ 1 and i a natural number.
  -- First, note that i + 2 ≥ 3 since i is a natural number.
  -- Therefore, 1/(i+2) ≤ 1/3 < 1/2.
  -- For x ≥ 1, the function f(k) = x^k is increasing.
  -- Hence, x^(1/(i+2)) ≤ x^(1/2).
  rw [Sqrt.eq.Root_2]
  -- Use the property that for x ≥ 1, the function x^k is increasing.
  -- This allows us to compare the exponents directly.
  apply Real.rpow_lt_rpow_of_exponent_lt h₀
  -- Show that 1/(i+2) ≤ 1/2 for all natural numbers i.
  rw [div_lt_div_iff₀]
  ·
    norm_num
    assumption
  ·
    linarith
  ·
    norm_num


-- created on 2025-04-06
