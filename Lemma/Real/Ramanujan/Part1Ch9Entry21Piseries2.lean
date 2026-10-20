import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry21Piseries2
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Filter Finset MeasureTheory
open Entry8Arcsin (chapter9OddHarmonic)
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry21Piseries2


/--
[ramanujan_part1_ch9_entry21_piseries2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry21Piseries2.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry21_piseries2_eq
  {x : ℝ}
-- given
  (hx : |x| ≤ Real.pi / 4) :
-- imply
  Summable chapter9Chi3Term ∧
    Summable (chapter9Entry21LeftTerm x) ∧
    Summable (chapter9Entry21SineTerm x) ∧
    Summable (chapter9Entry21CosineTerm x) ∧
    (∑' j : ℕ, chapter9Entry21LeftTerm x j) =
    chapter9TanLogTerm x +
    x * ∑' j : ℕ, chapter9Entry21SineTerm x j +
    (1 / 2 : ℝ) * ∑' j : ℕ, chapter9Entry21CosineTerm x j -
    (1 / 2 : ℝ) * chapter9Chi3AtOne := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry21Piseries2.ramanujan_part1_ch9_entry21_piseries2 x hx


-- created on 2026-10-20
