import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry23Ramanujanpi2
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Filter Finset Topology MeasureTheory
open Entry8Arcsin (chapter9OddHarmonic)
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry23Ramanujanpi2


/--
[ramanujan_part1_ch9_entry23_ramanujanpi2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry23Ramanujanpi2.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry23_ramanujanpi2_eq
  {x : ℝ}
-- given
  (hx : |x| ≤ Real.pi / 4) :
-- imply
  Summable (chapter9Entry23LeftTerm x) ∧
    Summable (chapter9Entry23FactorialTerm x) ∧
    Summable (chapter9Entry23FactorialTerm (2 * x)) ∧
    (∑' j : ℕ, chapter9Entry23LeftTerm x j) =
    2 * ∑' k : ℕ, chapter9Entry23FactorialTerm x k -
    (1 / 4 : ℝ) *
    ∑' k : ℕ, chapter9Entry23FactorialTerm (2 * x) k := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry23Ramanujanpi2.ramanujan_part1_ch9_entry23_ramanujanpi2 x hx


-- created on 2026-10-20
