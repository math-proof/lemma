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
  rw [Sqrt.eq.Root_2]
  apply Real.rpow_lt_rpow_of_exponent_lt h₀
  rw [div_lt_div_iff₀]
  ·
    norm_num
    assumption
  ·
    linarith
  ·
    norm_num


-- created on 2025-04-06
