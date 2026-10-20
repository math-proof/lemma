import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2
open Real Filter Topology intervalIntegral
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry3InfiniteEvaluation


/--
[ramanujan_part1_ch2_entry3_infinite_evaluation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry3_infinite_evaluation_eq
  :
-- imply
  HasSum (fun n : ℕ =>
    Real.arctan (10 * ((n : ℝ) + 1) /
    ((3 * ((n : ℝ) + 1) ^ 2 + 2) * (9 * ((n : ℝ) + 1) ^ 2 - 1))))
    (Real.log 3 - Real.pi / 4) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry3InfiniteEvaluation.ramanujan_part1_ch2_entry3_infinite_evaluation


-- created on 2026-10-20
