import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexSelectedBulkLogContribution_eq_logKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexSelectedBulkLogContribution_eq_logKernel_eq
  {c : Real}
  {J k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexSelectedBulkLogContribution hc J k = sixVertexSelectedBulkLogKernel hc J k := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedBulkLogContribution_eq_logKernel hc J k

/--
[sixVertexSelectedInitialLogContribution_le_factorial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexSelectedInitialLogContribution_le_factorial_eq
  {c : Real}
  {J k : Nat}
-- given
  (hc : 2 < c)
  (hJ : J ≤ k + 1) :
-- imply
  sixVertexSelectedInitialLogContribution hc J k ≤ (2 * ((J : Real) * Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2) - Real.log (J.factorial : Real))) / (sixVertexFourWidth 0 k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedInitialLogContribution_le_factorial hc hJ

/--
[sixVertexSelectedInitialLogContribution_le_stirling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexSelectedInitialLogContribution_le_stirling_eq
  {c : Real}
  {J k : Nat}
-- given
  (hc : 2 < c)
  (hJ0 : 0 < J)
  (hJ : J ≤ k + 1) :
-- imply
  sixVertexSelectedInitialLogContribution hc J k ≤ (2 * (J : Real) * (Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / (2 * (J : Real))) + 1)) / (sixVertexFourWidth 0 k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedInitialLogContribution_le_stirling hc hJ0 hJ

/--
[sixVertexSelectedInitialLogContribution_tendsto_zero_of_sublinear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexSelectedInitialLogContribution_tendsto_zero_of_sublinear_eq
  {c : Real}
  {J : Nat → Nat}
-- given
  (hc : 2 < c)
  (hJ0 : ∀ᶠ k in atTop, 0 < J k)
  (hJle : ∀ᶠ k in atTop, J k ≤ k + 1)
  (hsublinear : Tendsto (fun k : Nat => (J k : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0)) :
-- imply
  Tendsto (fun k => sixVertexSelectedInitialLogContribution hc (J k) k) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedInitialLogContribution_tendsto_zero_of_sublinear hc J hJ0 hJle hsublinear

/--
[sixVertexSelectedRootAverage_eq_initial_add_bulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexSelectedRootAverage_eq_initial_add_bulk_eq
  {c : Real}
  {J k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexSymmetricBetheRootAverage c (sixVertexPositiveHalfBetheRootFamily hc) k = sixVertexSelectedInitialLogContribution hc J k + sixVertexSelectedBulkLogContribution hc J k := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedRootAverage_eq_initial_add_bulk hc J k

/--
[sixVertexSelectedRootAverage_eq_log2Initial_add_bulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexSelectedRootAverage_eq_log2Initial_add_bulk_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexSymmetricBetheRootAverage c (sixVertexPositiveHalfBetheRootFamily hc) k = sixVertexSelectedInitialLogContribution hc (Nat.log2 (k + 1)) k + sixVertexSelectedBulkLogContribution hc (Nat.log2 (k + 1)) k := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedRootAverage_eq_log2Initial_add_bulk hc k

/--
[sixVertexHalfFilledBetheCandidateRate_eq_log2Edge_add_bulkKernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheCandidateRate_eq_log2Edge_add_bulkKernel_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexHalfFilledBetheCandidateRate hc k = Real.log 2 / (sixVertexFourWidth 0 k : Real) + sixVertexSelectedInitialLogContribution hc (Nat.log2 (k + 1)) k + sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheCandidateRate_eq_log2Edge_add_bulkKernel hc k

/--
[sixVertexSelectedRootAverage_tendsto_iff_bulkLog2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexSelectedRootAverage_tendsto_iff_bulkLog2_eq
  {c a : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexSymmetricBetheRootAverage c (sixVertexPositiveHalfBetheRootFamily hc)) atTop (nhds a) ↔ Tendsto (fun k => sixVertexSelectedBulkLogContribution hc (Nat.log2 (k + 1)) k) atTop (nhds a) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedRootAverage_tendsto_iff_bulkLog2 hc

/--
[sixVertexHalfFilledBetheCandidateRate_tendsto_iff_bulkLog2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheCandidateRate_tendsto_iff_bulkLog2_eq
  {c a : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexHalfFilledBetheCandidateRate hc) atTop (nhds a) ↔ Tendsto (fun k => sixVertexSelectedBulkLogContribution hc (Nat.log2 (k + 1)) k) atTop (nhds a) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheCandidateRate_tendsto_iff_bulkLog2 hc

/--
[sixVertexSelectedBulkFreeEnergyAsymptotic_iff_normContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexSelectedBulkFreeEnergyAsymptotic_iff_normContribution_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSelectedBulkFreeEnergyAsymptotic hc ↔ Tendsto (fun k => sixVertexSelectedBulkLogContribution hc (Nat.log2 (k + 1)) k) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedBulkFreeEnergyAsymptotic_iff_normContribution hc

/--
[sixVertexCentralWidthRate_tendsto_iff_bulkFreeEnergy_of_positivePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexCentralWidthRate_tendsto_iff_bulkFreeEnergy_of_positivePhase_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c) :
-- imply
  Tendsto (sixVertexCentralWidthRate c) atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c))) ↔ SixVertexSelectedBulkFreeEnergyAsymptotic hc := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralWidthRate_tendsto_iff_bulkFreeEnergy_of_positivePhase hc hphase

/--
[sixVertexBalanced_iteratedLimit_of_positivePhase_of_bulkFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean)
-/
@[path]
private lemma sixVertexBalanced_iteratedLimit_of_positivePhase_of_bulkFreeEnergy_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c)
  (hbulk : SixVertexSelectedBulkFreeEnergyAsymptotic hc) :
-- imply
  SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c) (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBalanced_iteratedLimit_of_positivePhase_of_bulkFreeEnergy hc hphase hbulk


-- created on 2026-10-23
