/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Asymptotics/MonotoneIntegralCriterion.lean -/


module

public import Theorem.Analysis.Asymptotics.MonotoneIntegralCriterion
public import Mathlib.NumberTheory.Chebyshev
public import Theorem.MathlibExtTest.Analysis.Asymptotics.MonotoneIntegralCriterion

@[expose] public section

open Filter MeasureTheory Set Topology Asymptotics


/-- A function agreeing with the identity on `[1, ∞)` but not globally monotone:
negation below `1`. This witnesses why `MonotoneOn` is the right hypothesis. -/
noncomputable def spikeBelowOne : ℝ → ℝ := fun x => if x < 1 then -x else x

