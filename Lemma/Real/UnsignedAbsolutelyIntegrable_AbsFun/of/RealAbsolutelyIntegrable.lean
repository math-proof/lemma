import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open RealAbsolutelyIntegrable


/--
[RealAbsolutelyIntegrable.abs](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ}
-- given
  (hf: RealAbsolutelyIntegrable f) :
-- imply
  UnsignedAbsolutelyIntegrable (EReal.abs_fun f) :=
-- proof
  RealAbsolutelyIntegrable.abs f hf


-- created on 2026-10-22
