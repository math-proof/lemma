/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch3Entry15Example1ExponentialSeries.lean -/


import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry15Example1ExponentialSeries
import Lemma.Nat.Ramanujan.Part1Ch3Entry15Example1ExponentialSeries

open scoped BigOperators

open MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry15Example1ExponentialSeries

-- The theorem specializes to the ordinary binomial series when `n = 1`.
example (m : ℝ) :
    HasSum (fun k : ℕ =>
      if k = 0 then (1 : ℝ)
      else (m * ∏ j ∈ Finset.range (k - 1), (m + (k : ℝ) - ((j : ℝ) + 1))) /
        ((2 : ℝ) ^ (k : ℝ) * (Nat.factorial k : ℝ))) ((2 : ℝ) ^ m) := by
  simpa using ramanujan_part1_ch3_entry15_example1_exponential_series m 1 (by norm_num)
    (by norm_num)
