import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open RealMeasurable


/--
[RealMeasurable.comp_cts](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ}
  {φ: ℝ → ℝ}
-- given
  (hf: RealMeasurable f)
  (hφ: Continuous φ) :
-- imply
  RealMeasurable (φ ∘ f) :=
-- proof
  RealMeasurable.comp_cts hf hφ


-- created on 2026-10-22
