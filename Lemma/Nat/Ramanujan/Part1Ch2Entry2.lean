import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry2
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry2


/--
[ramanujan_part1_ch2_entry2_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry2_general_eq
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.Icc 1 (2 * n + 1), (1 : ℝ) / ((n : ℝ) + (k : ℝ))) =
    1 + 2 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((3 * (k : ℝ)) ^ 3 - 3 * (k : ℝ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2.ramanujan_part1_ch2_entry2_general n

/--
[ramanujan_part1_ch2_entry2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry2_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∑ k ∈ Finset.Icc 1 (2 * n + 1), (1 : ℝ) / ((n : ℝ) + (k : ℝ))) =
    1 + 2 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((3 * (k : ℝ)) ^ 3 - 3 * (k : ℝ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2.ramanujan_part1_ch2_entry2 n hn


-- created on 2026-10-20
