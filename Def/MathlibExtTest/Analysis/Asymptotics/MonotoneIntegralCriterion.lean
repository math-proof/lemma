/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Asymptotics/MonotoneIntegralCriterion.lean -/


import sympy.atlas.Analysis.Asymptotics.MonotoneIntegralCriterion
import Mathlib.NumberTheory.Chebyshev
import Theorem.MathlibExtTest.Analysis.Asymptotics.MonotoneIntegralCriterion
open Filter MeasureTheory Set Topology Asymptotics


/-- A function agreeing with the identity on `[1, ∞)` but not globally monotone:
negation below `1`. This witnesses why `MonotoneOn` is the right hypothesis. -/
noncomputable def spikeBelowOne : ℝ → ℝ := fun x => if x < 1 then -x else x

