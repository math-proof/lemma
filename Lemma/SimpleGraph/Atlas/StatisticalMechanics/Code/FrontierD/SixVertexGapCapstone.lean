import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexGapCapstone
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexAntiferroelectricFreeEnergy_partialSum_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapCapstone.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricFreeEnergy_partialSum_tendsto_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Tendsto (fun N : Nat => lam / 2 + ∑ n ∈ range N, sixVertexFreeEnergySeriesTerm lam n) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricFreeEnergy_partialSum_tendsto hlam

/--
[sixVertexAntiferroelectricGapRate_eq_dualPowerSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapCapstone.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricGapRate_eq_dualPowerSeries_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexAntiferroelectricGapRate lam = sixVertexDualGapPowerSeries (Real.exp (-(Real.pi ^ 2) / (2 * lam))) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricGapRate_eq_dualPowerSeries hlam

/--
[sixVertexAntiferroelectricGapRate_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapCapstone.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricGapRate_pos_eq
  {lam : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  0 < sixVertexAntiferroelectricGapRate lam := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricGapRate_pos hlam

/--
[sixVertexAntiferroelectricGapFactor_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapCapstone.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricGapFactor_mem_Ioo_eq
  {lam : Real}
  {r : Nat}
-- given
  (hlam : 0 < lam)
  (hr : 1 <= r) :
-- imply
  Real.exp (-(r : Real) * sixVertexAntiferroelectricGapRate lam) ∈ Set.Ioo 0 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricGapFactor_mem_Ioo hlam hr

/--
[sixVertexCanonicalGapRate_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapCapstone.lean)
-/
@[path]
private lemma sixVertexCanonicalGapRate_pos_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalGapRate_pos hc

/--
[fkQgt4SixVertexGapRate_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapCapstone.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_pos_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_pos hq


-- created on 2026-10-23
