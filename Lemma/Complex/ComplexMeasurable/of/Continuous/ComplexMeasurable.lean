import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open ComplexMeasurable


/--
[ComplexMeasurable.comp_cts](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℂ}
  {φ: ℂ → ℂ}
-- given
  (hf: ComplexMeasurable f)
  (hφ: Continuous φ) :
-- imply
  ComplexMeasurable (φ ∘ f) :=
-- proof
  ComplexMeasurable.comp_cts hf hφ


-- created on 2026-10-22
