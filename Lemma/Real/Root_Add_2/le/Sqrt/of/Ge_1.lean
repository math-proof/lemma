import Lemma.Real.Sqrt.eq.Root_2
open Real


@[main]
private lemma main
  {x : ℝ}
  {i : ℕ}
-- given
  (h : x ≥ 1) :
-- imply
  x ^ (1 / (i + 2) : ℝ) ≤ √x := by
-- proof
  rw [Sqrt.eq.Root_2]
  apply Real.rpow_le_rpow_of_exponent_le h
  rw [div_le_div_iff₀]
  ·
    norm_num
  ·
    linarith
  ·
    norm_num


-- created on 2025-04-06
