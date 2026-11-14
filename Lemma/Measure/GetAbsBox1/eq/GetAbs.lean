import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Box
@[path]
private lemma main
  {I:BoundedInterval} :
-- imply
  |(I:Box 1)|ᵥ = |I|ₗ :=
-- proof
  Box.volume_of_interval I


-- created on 2026-10-22
