import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry3
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry3


/--
[ramanujan_part1_ch2_entry3_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry3.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry3_general_eq
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.Icc 1 (2 * n + 1), Real.arctan (1 / ((↑n + ↑k : ℝ))) =
    Real.pi / 4 + ∑ k ∈ Finset.Icc 1 n,
    Real.arctan ((10 * (↑k : ℝ)) / ((3 * (↑k : ℝ) ^ 2 + 2) * (9 * (↑k : ℝ) ^ 2 - 1))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3.ramanujan_part1_ch2_entry3_general n

/--
[ramanujan_part1_ch2_entry3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry3.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry3_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ∑ k ∈ Finset.Icc 1 (2 * n + 1), Real.arctan (1 / ((↑n + ↑k : ℝ))) =
    Real.pi / 4 + ∑ k ∈ Finset.Icc 1 n,
    Real.arctan ((10 * (↑k : ℝ)) / ((3 * (↑k : ℝ) ^ 2 + 2) * (9 * (↑k : ℝ) ^ 2 - 1))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3.ramanujan_part1_ch2_entry3 n hn


-- created on 2026-10-20
