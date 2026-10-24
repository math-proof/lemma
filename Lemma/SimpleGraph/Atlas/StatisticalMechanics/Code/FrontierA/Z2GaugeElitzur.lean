import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeElitzur
open Finset StatMech StatMech.FrontierA


/--
[gaugePartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeElitzur.lean)
-/
@[path]
private lemma gaugePartition_pos_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (incidence : P -> Finset E)
  (K : P -> ℝ) :
-- imply
  0 < gaugePartition incidence K := by
-- proof
  apply StatMech.FrontierA.gaugePartition_pos incidence K

/--
[gaugeWilsonNumerator_eq_zero_of_locallyCharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeElitzur.lean)
-/
@[path]
private lemma gaugeWilsonNumerator_eq_zero_of_locallyCharged_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E}
-- given
  (incidence : P -> Finset E)
  (star : Q -> Finset E)
  (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
  (K : P -> ℝ)
  (hcharged : IsLocallyGaugeCharged star L) :
-- imply
  gaugeWilsonNumerator incidence K L = 0 := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonNumerator_eq_zero_of_locallyCharged incidence star hcomplex K L hcharged

/--
[gaugeWilsonExpectation_eq_zero_of_locallyCharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeElitzur.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_eq_zero_of_locallyCharged_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E}
-- given
  (incidence : P -> Finset E)
  (star : Q -> Finset E)
  (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
  (K : P -> ℝ)
  (hcharged : IsLocallyGaugeCharged star L) :
-- imply
  gaugeWilsonExpectation incidence K L = 0 := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_eq_zero_of_locallyCharged incidence star hcomplex K L hcharged


-- created on 2026-10-23
