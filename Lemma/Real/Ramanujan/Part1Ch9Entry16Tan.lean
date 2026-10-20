import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry16Tan
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry16Tan


/--
[ramanujan_part1_ch9_entry16_tan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tan.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry16_tan_eq
  {x : ℝ}
-- given
  (hx : |x| ≤ Real.pi / 2) :
-- imply
  (x ≠ 0 → 0 < |2 * Real.sin x|) ∧
    Summable (Entry16Tanseries.chapter9CentralSineTerm x) ∧
    Summable (chapter9SineFourierTwoTerm x) ∧
    (∑' k : ℕ, Entry16Tanseries.chapter9CentralSineTerm x k) =
    chapter9Entry16LogTerm x +
    (1 / 2 : ℝ) * ∑' j : ℕ, chapter9SineFourierTwoTerm x j := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tan.ramanujan_part1_ch9_entry16_tan x hx


-- created on 2026-10-20
