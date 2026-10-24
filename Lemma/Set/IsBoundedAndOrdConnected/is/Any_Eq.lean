import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/--
[BoundedInterval.ordConnected_iff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {X:Set ℝ} :
-- imply
  Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I :=
-- proof
  BoundedInterval.ordConnected_iff X


-- created on 2026-10-22
