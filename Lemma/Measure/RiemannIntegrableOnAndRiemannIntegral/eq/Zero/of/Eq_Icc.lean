import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open RiemannIntegrable
@[path]
private lemma main
  {f: ℝ → ℝ}
  {I: BoundedInterval}
  {a : ℝ}
-- given
  (h: I = Icc a a) :
-- imply
  RiemannIntegrableOn f I ∧ riemannIntegral f I = 0 :=
-- proof
  RiemannIntegrable.of_zero_length f h


-- created on 2026-10-22
