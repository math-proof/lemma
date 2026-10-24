import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_4
open UnsignedLebesgueIntegral


/--
[UnsignedLebesgueIntegral.nonneg](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → EReal}
-- given
  (hf: UnsignedMeasurable f) :
-- imply
  0 ≤ UnsignedLebesgueIntegral f :=
-- proof
  UnsignedLebesgueIntegral.nonneg hf


-- created on 2026-10-22
