import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry4
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry4


/--
[ramanujan_part1_ch2_entry4_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry4_general_eq
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ))) + (∑ k ∈ Finset.Icc 0 n, (1 : ℝ) /
    (2 * (n : ℝ) + 2 * (k : ℝ) + 1)) =
    1 + 2 * (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4.ramanujan_part1_ch2_entry4_general n

/--
[ramanujan_part1_ch2_entry4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry4_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ))) + (∑ k ∈ Finset.Icc 0 n, (1 : ℝ) /
    (2 * (n : ℝ) + 2 * (k : ℝ) + 1)) =
    1 + 2 * (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4.ramanujan_part1_ch2_entry4 n hn


-- created on 2026-10-20
