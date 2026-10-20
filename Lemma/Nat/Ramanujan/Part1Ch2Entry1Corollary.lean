import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry1Corollary
open Filter Topology
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry1Corollary


/--
[ramanujan_part1_ch2_entry1_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry1Corollary.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry1_corollary_eq
  :
-- imply
  HasSum (fun n : ℕ => (1 : ℝ) / ((2 * (↑(n + 1) : ℝ)) ^ 3 - 2 * (↑(n + 1) : ℝ)))
    (Real.log 2 - 1 / 2) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry1Corollary.ramanujan_part1_ch2_entry1_corollary


-- created on 2026-10-20
