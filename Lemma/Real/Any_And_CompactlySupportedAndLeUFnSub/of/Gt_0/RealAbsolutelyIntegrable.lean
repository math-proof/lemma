import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_5
open RealAbsolutelyIntegrable


/--
[RealAbsolutelyIntegrable.approx_by_continuous_compact](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_5.lean)
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
  ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
          PreL1.norm (f - g) ≤ ε :=
-- proof
  RealAbsolutelyIntegrable.approx_by_continuous_compact hf ε hε


-- created on 2026-10-22
