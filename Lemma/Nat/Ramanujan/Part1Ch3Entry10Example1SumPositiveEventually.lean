import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10Example1SumPositiveEventually
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry10Example1SumPositiveEventually


/--
[ramanujan_part1_ch3_entry10_example1_sum_positive_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example1SumPositiveEventually.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry10_example1_sum_positive_eventually_eq
  :
-- imply
  ∀ᶠ (x : ℝ) in Filter.atTop, 0 < ∑' (j : ℕ), x ^ (j + 1) * Real.sqrt (↑(j + 1)) /
    (↑(Nat.factorial (j + 1)) : ℝ) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example1SumPositiveEventually.ramanujan_part1_ch3_entry10_example1_sum_positive_eventually


-- created on 2026-10-20
