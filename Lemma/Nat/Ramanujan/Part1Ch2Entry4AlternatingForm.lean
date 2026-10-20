import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry4AlternatingForm
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry4AlternatingForm


/--
[ramanujan_part1_ch2_entry4_alternating_form_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4AlternatingForm.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry4_alternating_form_general_eq
  {n : ℕ} :
-- imply
  (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 n, (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) =
    (∑ k ∈ Finset.Icc 1 (4 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
    (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 (2 * n), ((-1 : ℝ) ^ (k + 1) / (k : ℝ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4AlternatingForm.ramanujan_part1_ch2_entry4_alternating_form_general n

/--
[ramanujan_part1_ch2_entry4_alternating_form](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4AlternatingForm.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry4_alternating_form_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 n, (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) =
    (∑ k ∈ Finset.Icc 1 (4 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
    (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 (2 * n), ((-1 : ℝ) ^ (k + 1) / (k : ℝ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4AlternatingForm.ramanujan_part1_ch2_entry4_alternating_form n hn


-- created on 2026-10-20
