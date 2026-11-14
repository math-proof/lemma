import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_11_4
open Chapter9
open Chapter11
open Chapter11.IntegrableOn
@[path]
private lemma main
  {I: BoundedInterval}
  {f:ℝ → ℝ}
-- given
  (hf: IntegrableOn f I) :
-- imply
  IntegrableOn (abs f) I :=
-- proof
  Chapter11.IntegrableOn.abs hf


-- created on 2026-10-22
