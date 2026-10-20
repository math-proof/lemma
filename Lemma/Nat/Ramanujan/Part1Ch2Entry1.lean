import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry1
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry1


/--
[ramanujan_part1_ch2_entry1_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry1.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry1_general_eq
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) =
    (n : ℝ) / (2 * (n : ℝ) + 1) + ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) /
    ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry1.ramanujan_part1_ch2_entry1_general n

/--
[ramanujan_part1_ch2_entry1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry1.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry1_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) =
    (n : ℝ) / (2 * (n : ℝ) + 1) + ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) /
    ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry1.ramanujan_part1_ch2_entry1 n hn


-- created on 2026-10-20
