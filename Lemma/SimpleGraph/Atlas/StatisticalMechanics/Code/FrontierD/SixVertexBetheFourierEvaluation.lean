import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFreeEnergyPairedFourierTerm_eq_seriesTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean)
-/
@[path]
private lemma sixVertexFreeEnergyPairedFourierTerm_eq_seriesTerm_eq
  {lam : Real}
  {n : Nat} :
-- imply
  sixVertexFreeEnergyPairedFourierTerm lam n = sixVertexFreeEnergySeriesTerm lam n := by
-- proof
  apply StatMech.FrontierD.sixVertexFreeEnergyPairedFourierTerm_eq_seriesTerm lam n

/--
[sixVertexFreeEnergyFourierPartialSum_eq_seriesPartialSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean)
-/
@[path]
private lemma sixVertexFreeEnergyFourierPartialSum_eq_seriesPartialSum_eq
  {lam : Real}
  {N : Nat} :
-- imply
  sixVertexFreeEnergyFourierPartialSum lam N = lam / 2 + ∑ n ∈ range N, sixVertexFreeEnergySeriesTerm lam n := by
-- proof
  apply StatMech.FrontierD.sixVertexFreeEnergyFourierPartialSum_eq_seriesPartialSum lam N

/--
[sixVertexFreeEnergyFourierPartialSum_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean)
-/
@[path]
private lemma sixVertexFreeEnergyFourierPartialSum_tendsto_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Tendsto (sixVertexFreeEnergyFourierPartialSum lam) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFreeEnergyFourierPartialSum_tendsto hlam

/--
[sixVertexOffsetFourierPartialSum_eq_gapPartialSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean)
-/
@[path]
private lemma sixVertexOffsetFourierPartialSum_eq_gapPartialSum_eq
  {lam : Real}
  {N : Nat} :
-- imply
  sixVertexOffsetFourierPartialSum lam N = lam + 2 * ∑ n ∈ range N, sixVertexGapSeriesTerm lam n := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetFourierPartialSum_eq_gapPartialSum lam N

/--
[sixVertexOffsetFourierPartialSum_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean)
-/
@[path]
private lemma sixVertexOffsetFourierPartialSum_tendsto_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Tendsto (sixVertexOffsetFourierPartialSum lam) atTop (nhds (sixVertexAntiferroelectricGapRate lam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexOffsetFourierPartialSum_tendsto hlam

/--
[sixVertexSelectedBulkFreeEnergyAsymptotic_iff_matchesRootDensityFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean)
-/
@[path]
private lemma sixVertexSelectedBulkFreeEnergyAsymptotic_iff_matchesRootDensityFourier_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSelectedBulkFreeEnergyAsymptotic hc ↔ SixVertexSelectedBulkMatchesRootDensityFourier hc := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedBulkFreeEnergyAsymptotic_iff_matchesRootDensityFourier hc

/--
[sixVertexFixedChargeLogRatio_tendsto_iff_matchesOffsetFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean)
-/
@[path]
private lemma sixVertexFixedChargeLogRatio_tendsto_iff_matchesOffsetFourier_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexFixedChargeLogRatio c r) atTop (nhds (-(r : Real) * sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c))) ↔ SixVertexFixedChargeMatchesOffsetFourier c r := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLogRatio_tendsto_iff_matchesOffsetFourier hc r

/--
[sixVertexFixedChargeRatio_tendsto_iff_matchesOffsetFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean)
-/
@[path]
private lemma sixVertexFixedChargeRatio_tendsto_iff_matchesOffsetFourier_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexFixedChargeRatio c r) atTop (nhds (Real.exp (-(r : Real) * sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c)))) ↔ SixVertexFixedChargeMatchesOffsetFourier c r := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeRatio_tendsto_iff_matchesOffsetFourier hc r

/--
[sixVertexAntiferroelectricTransferConclusion_of_rootDensityFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricTransferConclusion_of_rootDensityFourier_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c)
  (hbulk : SixVertexSelectedBulkMatchesRootDensityFourier hc)
  (hoffset : ∀ r : Nat, 1 ≤ r → SixVertexFixedChargeMatchesOffsetFourier c r) :
-- imply
  SixVertexAntiferroelectricTransferConclusion c (sixVertexAntiferroelectricLambda c) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricTransferConclusion_of_rootDensityFourier hc hphase hbulk hoffset


-- created on 2026-10-23
