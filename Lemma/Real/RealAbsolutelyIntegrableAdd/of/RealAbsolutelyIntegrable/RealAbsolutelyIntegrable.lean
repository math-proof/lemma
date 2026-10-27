import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open RealAbsolutelyIntegrable


/--
[RealAbsolutelyIntegrable.add](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → ℝ}
-- given
  (hf: RealAbsolutelyIntegrable f)
  (hg: RealAbsolutelyIntegrable g) :
-- imply
  RealAbsolutelyIntegrable (f + g) :=
-- proof
  RealAbsolutelyIntegrable.add hf hg


-- created on 2026-10-22
