import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open UnsignedMeasurable


/--
[UnsignedMeasurable.add](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f g: EuclideanSpace' d → EReal}
-- given
  (hf: UnsignedMeasurable f)
  (hg: UnsignedMeasurable g) :
-- imply
  UnsignedMeasurable (f + g) :=
-- proof
  UnsignedMeasurable.add hf hg


-- created on 2026-10-22
