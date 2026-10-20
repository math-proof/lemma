import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry5
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry5


/--
[ramanujan_part1_ch2_entry5_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry5.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry5_general_eq
  {n : ℕ} :
-- imply
  (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((6 * (k : ℝ)) ^ 3 - 6 * (k : ℝ)) =
    (2 : ℝ) / 3 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) +
    ∑ k ∈ Finset.Icc 0 (2 * n), (1 : ℝ) / (2 * (n : ℝ) + 2 * (k : ℝ) + 1) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry5.ramanujan_part1_ch2_entry5_general n

/--
[ramanujan_part1_ch2_entry5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry5.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry5_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((6 * (k : ℝ)) ^ 3 - 6 * (k : ℝ)) =
    (2 : ℝ) / 3 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) +
    ∑ k ∈ Finset.Icc 0 (2 * n), (1 : ℝ) / (2 * (n : ℝ) + 2 * (k : ℝ) + 1) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry5.ramanujan_part1_ch2_entry5 n hn


-- created on 2026-10-20
