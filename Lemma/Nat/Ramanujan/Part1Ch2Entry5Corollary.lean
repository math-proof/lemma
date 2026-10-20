import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry5Corollary
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry5Corollary


/--
[ramanujan_part1_ch2_entry5_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry5Corollary.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry5_corollary_eq
  :
-- imply
  HasSum (fun j : ℕ => (2 : ℝ) / ((6 * (↑j + 1)) ^ 3 - 6 * (↑j + 1)))
    (1 / 2 * Real.log 3 + 1 / 3 * Real.log 4 - 1) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry5Corollary.ramanujan_part1_ch2_entry5_corollary


-- created on 2026-10-20
