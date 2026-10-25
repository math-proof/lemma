import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
open EReal


/--
[EReal.indicator_eq_comp](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {A: Set X} :
-- imply
  EReal.indicator A = Real.toEReal ∘ A.indicator' :=
-- proof
  EReal.indicator_eq_comp A


-- created on 2026-10-22
