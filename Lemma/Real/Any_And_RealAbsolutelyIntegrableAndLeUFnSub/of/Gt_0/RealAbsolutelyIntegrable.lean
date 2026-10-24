import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_5
open RealAbsolutelyIntegrable


/--
[RealAbsolutelyIntegrable.approx_by_simple](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_5.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ}
  {ε : ℝ}
-- given
  (hf : RealAbsolutelyIntegrable f)
  (hε : 0 < ε) :
-- imply
  ∃ (g : EuclideanSpace' d → ℝ), RealSimpleFunction g ∧ RealAbsolutelyIntegrable g ∧
      PreL1.norm (f - g) ≤ ε :=
-- proof
  RealAbsolutelyIntegrable.approx_by_simple hf ε hε


-- created on 2026-10-22
