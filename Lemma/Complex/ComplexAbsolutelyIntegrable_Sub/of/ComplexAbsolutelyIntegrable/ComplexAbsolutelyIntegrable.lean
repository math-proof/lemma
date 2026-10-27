import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.sub](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → ℂ}
-- given
  (hf: ComplexAbsolutelyIntegrable f)
  (hg: ComplexAbsolutelyIntegrable g) :
-- imply
  ComplexAbsolutelyIntegrable (f - g) :=
-- proof
  ComplexAbsolutelyIntegrable.sub hf hg


-- created on 2026-10-22
