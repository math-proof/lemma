import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Box


/--
[Box.volume_of_interval](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I:BoundedInterval} :
-- imply
  |(I:Box 1)|ᵥ = |I|ₗ :=
-- proof
  Box.volume_of_interval I


-- created on 2026-10-22
