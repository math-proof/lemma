import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonRatio
open Finset StatMech StatMech.FrontierA


/--
[gaugeHighTempPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonRatio.lean)
-/
@[path]
private lemma gaugeHighTempPrefactor_pos_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (K : P -> ℝ) :
-- imply
  0 < (2 : ℝ) ^ Fintype.card E * ∏ p : P, Real.cosh (K p) := by
-- proof
  apply StatMech.FrontierA.gaugeHighTempPrefactor_pos K

/--
[gaugeClosedSurfaceSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonRatio.lean)
-/
@[path]
private lemma gaugeClosedSurfaceSum_pos_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (incidence : P -> Finset E)
  (K : P -> ℝ) :
-- imply
  0 < gaugeClosedSurfaceSum incidence K := by
-- proof
  apply StatMech.FrontierA.gaugeClosedSurfaceSum_pos incidence K

/--
[gaugeWilsonExpectation_eq_surfaceRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonRatio.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_eq_surfaceRatio_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E}
-- given
  (incidence : P -> Finset E)
  (K : P -> ℝ) :
-- imply
  gaugeWilsonExpectation incidence K L = gaugeWilsonSurfaceSum incidence K L / gaugeClosedSurfaceSum incidence K := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_eq_surfaceRatio incidence K L


-- created on 2026-10-23
