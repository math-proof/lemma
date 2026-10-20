import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry34Zeta3doublesum
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry8Arcsin (chapter9OddHarmonic)
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry34Zeta3doublesum


/--
[ramanujan_part1_ch9_entry34_zeta3doublesum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry34Zeta3doublesum.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry34_zeta3doublesum_eq
  {x : ℝ}
-- given
  (hxLower : -(1 / 2 : ℝ) < x)
  (hxUpper : x < 1) :
-- imply
  0 < 1 + x ∧
    |x| < 1 ∧
    |x / (1 + x)| < 1 ∧
    Summable (chapter9Entry34LeftTerm x) ∧
    Summable (chapter9Entry34RightTerm x) ∧
    (∑' k : ℕ, chapter9Entry34LeftTerm x k) =
    ∑' k : ℕ, chapter9Entry34RightTerm x k := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry34Zeta3doublesum.ramanujan_part1_ch9_entry34_zeta3doublesum x hxLower hxUpper


-- created on 2026-10-20
