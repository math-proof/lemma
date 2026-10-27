import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
open Finset Matrix Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFourWidth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexFourWidth_pos_eq
  {r k : ℕ} :
-- imply
  0 < sixVertexFourWidth r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFourWidth_pos r k

/--
[sixVertexFourWidth_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexFourWidth_even_eq
  {r k : ℕ} :
-- imply
  Even (sixVertexFourWidth r k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourWidth_even r k

/--
[sixVertexFourWidth_charge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexFourWidth_charge_le_eq
  {r k : ℕ} :
-- imply
  r ≤ sixVertexFourWidth r k / 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourWidth_charge_le r k

/--
[sixVertexLambdaAlongFour_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexLambdaAlongFour_pos_eq
  {c : ℝ}
  {r k : ℕ}
-- given
  (hc : 0 < c) :
-- imply
  0 < sixVertexLambdaAlongFour c r k := by
-- proof
  apply StatMech.FrontierD.sixVertexLambdaAlongFour_pos hc r k

/--
[sixVertexFixedChargeRatio_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeRatio_pos_eq
  {c : ℝ}
  {r k : ℕ}
-- given
  (hc : 0 < c) :
-- imply
  0 < sixVertexFixedChargeRatio c r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeRatio_pos hc r k

/--
[sixVertexFixedChargeLogRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeLogRatio_eq_eq
  {c : ℝ}
  {r k : ℕ}
-- given
  (hc : 0 < c) :
-- imply
  sixVertexFixedChargeLogRatio c r k = Real.log (sixVertexLambdaAlongFour c r k) - Real.log (sixVertexLambda (sixVertexFourWidth r k) 0 (sixVertexFourWidth_even r k) (Nat.zero_le _) c) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLogRatio_eq hc r k

/--
[sixVertexFixedChargeTraceLogRatio_div_height_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeTraceLogRatio_div_height_tendsto_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (fun M : Nat => Real.log (Matrix.trace (sixVertexSectorTransfer (sixVertexFourWidth r k) (sixVertexFourWidth r k / 2 - r) c ^ M) / Matrix.trace (sixVertexSectorTransfer (sixVertexFourWidth r k) (sixVertexFourWidth r k / 2) c ^ M)) / (M : Real)) atTop (nhds (sixVertexFixedChargeLogRatio c r k)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeTraceLogRatio_div_height_tendsto hc r k

/--
[sixVertexFixedChargeRatio_tendsto_iff_logRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexFixedChargeRatio_tendsto_iff_logRatio_eq
  {c L : ℝ}
  {r : ℕ}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (sixVertexFixedChargeRatio c r) atTop (nhds (Real.exp L)) ↔ Tendsto (sixVertexFixedChargeLogRatio c r) atTop (nhds L) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeRatio_tendsto_iff_logRatio hc r

/--
[sixVertexAntiferroelectricGapFormula_iff_logBethe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricGapFormula_iff_logBethe_eq
  {c lam : ℝ}
  {r : ℕ}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (sixVertexFixedChargeRatio c r) atTop (nhds (Real.exp (-(r : ℝ) * sixVertexAntiferroelectricGapRate lam))) ↔ Tendsto (sixVertexFixedChargeLogRatio c r) atTop (nhds (-(r : ℝ) * sixVertexAntiferroelectricGapRate lam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricGapFormula_iff_logBethe hc r

/--
[sixVertexBalancedAreaDensity_tendsto_widthRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexBalancedAreaDensity_tendsto_widthRate_eq
  {c : ℝ}
  {k : ℕ}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (sixVertexBalancedAreaDensity c k) atTop (nhds (sixVertexCentralWidthRate c k)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBalancedAreaDensity_tendsto_widthRate hc k

/--
[sixVertexBalanced_iteratedLimit_iff_widthRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexBalanced_iteratedLimit_iff_widthRate_eq
  {c a : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c) a ↔ Tendsto (sixVertexCentralWidthRate c) atTop (nhds a) := by
-- proof
  apply StatMech.FrontierD.sixVertexBalanced_iteratedLimit_iff_widthRate hc

/--
[sixVertexAntiferroelectricFreeEnergyFormula_iff_widthBethe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricFreeEnergyFormula_iff_widthBethe_eq
  {c lam : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c) (sixVertexAntiferroelectricFreeEnergyValue lam) ↔ Tendsto (sixVertexCentralWidthRate c) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricFreeEnergyFormula_iff_widthBethe hc


-- created on 2026-10-23
