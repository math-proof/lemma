import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeThermodynamicReduction.Part2
open Filter Set Topology StatMech StatMech.FrontierA


/--
[eventual_areaLaw_of_logDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean)
-/
@[path]
private lemma eventual_areaLaw_of_logDensity_tendsto_eq
  {w : Nat → Real}
  {tau : Real}
-- given
  (hw : ∀ n, 0 < w n)
  (hlim : Tendsto (fun n : Nat => -Real.log (w n) / ((n + 1 : Nat) : Real) ^ 2) atTop (nhds tau))
  (htau : 0 < tau) :
-- imply
  ∀ᶠ n : Nat in atTop, w n ≤ Real.exp (-(tau / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.eventual_areaLaw_of_logDensity_tendsto w tau hw hlim htau

/--
[eventual_perimeterLaw_of_negLog_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean)
-/
@[path]
private lemma eventual_perimeterLaw_of_negLog_le_eq
  {w : Nat → Real}
  {C : Real}
-- given
  (hw : ∀ n, 0 < w n)
  (hcost : ∀ᶠ n : Nat in atTop, -Real.log (w n) ≤ C * ((n + 1 : Nat) : Real)) :
-- imply
  ∀ᶠ n : Nat in atTop, Real.exp (-C * ((n + 1 : Nat) : Real)) ≤ w n := by
-- proof
  apply StatMech.FrontierA.eventual_perimeterLaw_of_negLog_le w C hw hcost

/--
[cubicalSquareWilsonExpectation_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean)
-/
@[path]
private lemma cubicalSquareWilsonExpectation_pos_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 < cubicalSquareWilsonExpectation beta n := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilsonExpectation_pos hbeta n

/--
[cubicalSquareWilsonFreeEnergy_eq_neg_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean)
-/
@[path]
private lemma cubicalSquareWilsonFreeEnergy_eq_neg_log_eq
  {beta : Real}
  {n : Nat} :
-- imply
  cubicalSquareWilsonFreeEnergy beta n = -Real.log (cubicalSquareWilsonExpectation beta n) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilsonFreeEnergy_eq_neg_log beta n

/--
[cubicalSquareWilson_eventually_areaLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean)
-/
@[path]
private lemma cubicalSquareWilson_eventually_areaLaw_eq
  {beta tau : Real}
-- given
  (hbeta : 0 < beta)
  (hlim : Tendsto (cubicalSquareWilsonDensity beta) atTop (nhds tau))
  (htau : 0 < tau) :
-- imply
  ∀ᶠ n : Nat in atTop, cubicalSquareWilsonExpectation beta n ≤ Real.exp (-(tau / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilson_eventually_areaLaw hbeta hlim htau

/--
[cubicalSquareWilson_eventually_perimeterLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean)
-/
@[path]
private lemma cubicalSquareWilson_eventually_perimeterLaw_eq
  {beta C : Real}
-- given
  (hbeta : 0 < beta)
  (hcost : ∀ᶠ n : Nat in atTop, cubicalSquareWilsonFreeEnergy beta n ≤ C * ((n + 1 : Nat) : Real)) :
-- imply
  ∀ᶠ n : Nat in atTop, Real.exp (-C * ((n + 1 : Nat) : Real)) ≤ cubicalSquareWilsonExpectation beta n := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilson_eventually_perimeterLaw hbeta hcost

/--
[cubicalSquareWilson_rate_pos_iff_below_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean)
-/
@[path]
private lemma cubicalSquareWilson_rate_pos_iff_below_critical_eq
  {betaGauge betaIsingC tau : Real}
  {isingSurfaceTension : Real → Real}
-- given
  (hGauge : 0 < betaGauge)
  (hIsingC : 0 < betaIsingC)
  (hidentify : tau = isingSurfaceTension (gaugeDualCoupling betaGauge))
  (hphase : 0 < isingSurfaceTension (gaugeDualCoupling betaGauge) ↔ betaIsingC < gaugeDualCoupling betaGauge) :
-- imply
  0 < tau ↔ betaGauge < gaugeCriticalCoupling betaIsingC := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilson_rate_pos_iff_below_critical hGauge hIsingC isingSurfaceTension hidentify hphase

/--
[cubicalSquareWilson_areaLaw_of_dual_surfaceTension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean)
-/
@[path]
private lemma cubicalSquareWilson_areaLaw_of_dual_surfaceTension_eq
  {betaGauge betaIsingC tau : Real}
  {isingSurfaceTension : Real → Real}
-- given
  (hGauge : 0 < betaGauge)
  (hIsingC : 0 < betaIsingC)
  (hlim : Tendsto (cubicalSquareWilsonDensity betaGauge) atTop (nhds tau))
  (hidentify : tau = isingSurfaceTension (gaugeDualCoupling betaGauge))
  (hphase : 0 < isingSurfaceTension (gaugeDualCoupling betaGauge) ↔ betaIsingC < gaugeDualCoupling betaGauge)
  (hbelow : betaGauge < gaugeCriticalCoupling betaIsingC) :
-- imply
  ∀ᶠ n : Nat in atTop, cubicalSquareWilsonExpectation betaGauge n ≤ Real.exp (-(tau / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilson_areaLaw_of_dual_surfaceTension hGauge hIsingC isingSurfaceTension hlim hidentify hphase hbelow


-- created on 2026-10-23
