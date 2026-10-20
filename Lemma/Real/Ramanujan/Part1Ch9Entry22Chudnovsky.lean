import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry22Chudnovsky
open MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries
open scoped Nat Real BigOperators Interval
open Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry22Chudnovsky


/--
[chapter9Chi3Term_eq_entry21](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry22Chudnovsky.lean)
-/
@[path]
private lemma chapter9Chi3Term_eq_entry21_eq
  :
-- imply
  chapter9Chi3Term = Entry21Piseries2.chapter9Chi3Term := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry22Chudnovsky.chapter9Chi3Term_eq_entry21

/--
[chapter9Chi3AtOne_eq_entry21](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry22Chudnovsky.lean)
-/
@[path]
private lemma chapter9Chi3AtOne_eq_entry21_eq
  :
-- imply
  chapter9Chi3AtOne = Entry21Piseries2.chapter9Chi3AtOne := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry22Chudnovsky.chapter9Chi3AtOne_eq_entry21

/--
[chapter9Entry23FactorialTerm_eq_entry20](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry22Chudnovsky.lean)
-/
@[path]
private lemma chapter9Entry23FactorialTerm_eq_entry20_eq
  :
-- imply
  chapter9Entry23FactorialTerm = Entry20Piseries1.chapter9Entry23FactorialTerm := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry22Chudnovsky.chapter9Entry23FactorialTerm_eq_entry20

/--
[ramanujan_part1_ch9_entry22_chudnovsky](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry22Chudnovsky.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry22_chudnovsky_eq
  {x : ℝ}
-- given
  (hx0 : 0 ≤ x)
  (hx : x ≤ Real.pi / 4) :
-- imply
  0 < 2 * Real.cos x ∧
    Summable chapter9Chi3Term ∧
    Summable (chapter9Entry22LeftTerm x) ∧
    Summable (chapter9Entry22CentralTerm x) ∧
    Summable (chapter9Entry23FactorialTerm (2 * x)) ∧
    (∑' k : ℕ, chapter9Entry22LeftTerm x k) =
    -(Real.pi ^ 2 / 8) * Real.log (2 * Real.cos x) +
    Real.pi / 2 * ∑' k : ℕ, chapter9Entry22CentralTerm x k +
    (1 / 4 : ℝ) *
    ∑' k : ℕ, chapter9Entry23FactorialTerm (2 * x) k -
    (1 / 2 : ℝ) * chapter9Chi3AtOne := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry22Chudnovsky.ramanujan_part1_ch9_entry22_chudnovsky x hx0 hx


-- created on 2026-10-20
