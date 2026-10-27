import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
open scoped Pointwise


/--
[rat_Icc_countable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  Set.Countable {q : ℚ | q ∈ Set.Icc (-1:ℚ) 1} :=
-- proof
  rat_Icc_countable


-- created on 2026-10-22
