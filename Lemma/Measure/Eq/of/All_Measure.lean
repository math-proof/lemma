import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_4_3
open CountablyAdditiveMeasure


/--
[CountablyAdditiveMeasure.ext](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_4_3.lean)
-/
@[path]
private lemma main
  {B: ConcreteSigmaAlgebra X}
  {μ ν : CountablyAdditiveMeasure B}
-- given
  (h : ∀ A, μ.measure A = ν.measure A) :
-- imply
  μ = ν :=
-- proof
  CountablyAdditiveMeasure.ext h


-- created on 2026-10-22
