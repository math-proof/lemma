import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
@[path]
private lemma main
  {I₁ I₂ : BoundedInterval}
-- given
  (h : I₁.bisect.fst = I₂.bisect.fst) :
-- imply
  I₁.a = I₂.a ∧ I₁.b = I₂.b :=
-- proof
  BoundedInterval.bisect_fst_eq_endpoints h


-- created on 2026-10-22
