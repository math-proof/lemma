import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open UnsignedMeasurable


/--
[UnsignedMeasurable.comp_cts](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → EReal}
  {φ: EReal → EReal}
-- given
  (hf: UnsignedMeasurable f)
  (hφ: Continuous φ)
  (hφnn : ∀ x ≥ 0, φ x ≥ 0) :
-- imply
  UnsignedMeasurable (φ ∘ f) :=
-- proof
  UnsignedMeasurable.comp_cts hf hφ hφnn


-- created on 2026-10-22
