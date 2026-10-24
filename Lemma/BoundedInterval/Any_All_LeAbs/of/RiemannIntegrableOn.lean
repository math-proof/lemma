import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_3
open BoundedInterval
open RiemannIntegrable


/--
[RiemannIntegrable.bounded](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {f: ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (h: RiemannIntegrableOn f I) :
-- imply
  ∃ M, ∀ x ∈ I, |f x| ≤ M :=
-- proof
  RiemannIntegrable.bounded h


-- created on 2026-10-22
