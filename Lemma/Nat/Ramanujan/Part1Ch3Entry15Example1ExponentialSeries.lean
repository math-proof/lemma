import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry15Example1ExponentialSeries
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry15Example1ExponentialSeries


/--
[ramanujan_part1_ch3_entry15_example1_exponential_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry15Example1ExponentialSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry15_example1_exponential_series_eq
  {m n : ℝ}
-- given
  (hn_pos : 0 < n)
  (hn_le : n ≤ 2) :
-- imply
  HasSum (fun k : ℕ =>
    if k = 0 then (1 : ℝ)
    else (m * ∏ j ∈ Finset.range (k - 1), (m + (k : ℝ) * n - ((j : ℝ) + 1))) /
    ((2 : ℝ) ^ ((k : ℝ) * n) * (Nat.factorial k : ℝ))) ((2 : ℝ) ^ m) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry15Example1ExponentialSeries.ramanujan_part1_ch3_entry15_example1_exponential_series m n hn_pos hn_le


-- created on 2026-10-20
