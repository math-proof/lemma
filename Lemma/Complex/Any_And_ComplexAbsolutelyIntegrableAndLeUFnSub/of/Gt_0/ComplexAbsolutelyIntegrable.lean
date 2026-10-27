import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Section_1_3_5.Part3
open ComplexAbsolutelyIntegrable


/--
[ComplexAbsolutelyIntegrable.approx_by_simple](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_5.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
  {ε : ℝ}
-- given
  (hf : ComplexAbsolutelyIntegrable f)
  (hε : 0 < ε) :
-- imply
  ∃ (g : EuclideanSpace' d → ℂ), ComplexSimpleFunction g ∧ ComplexAbsolutelyIntegrable g ∧
      PreL1.norm (f - g) ≤ ε :=
-- proof
  ComplexAbsolutelyIntegrable.approx_by_simple hf ε hε


-- created on 2026-10-22
