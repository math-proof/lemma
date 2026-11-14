import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open RiemannIntegrable
@[path]
private lemma main
  {f: ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (h: RiemannIntegrableOn f I) :
-- imply
  ∃ M, ∀ x ∈ I, |f x| ≤ M :=
-- proof
  RiemannIntegrable.bounded h


-- created on 2026-10-22
