import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAllSectorVerticalRate.Part2
open Filter Topology StatMech StatMech.FrontierD


/--
[fkRectFixedChargeVerticalFamily_criticalReducedZ_eq_boundaryTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAllSectorVerticalRate.lean)
-/
@[path]
private lemma fkRectFixedChargeVerticalFamily_criticalReducedZ_eq_boundaryTransfer_eq
  {r k m : Nat}
  {q : Real} :
-- imply
  fkRectCriticalReducedZ (fkRectFixedChargeVerticalFamily r k m) q = fkRectBoundaryTransferReducedZ (fkRectFixedChargeVerticalFamily r k m).width_pos q (m + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeVerticalFamily_criticalReducedZ_eq_boundaryTransfer r k m q

/--
[exists_fkRectFixedChargeVerticalFamily_criticalReducedZ_log_div_height_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAllSectorVerticalRate.lean)
-/
@[path]
private lemma exists_fkRectFixedChargeVerticalFamily_criticalReducedZ_log_div_height_tendsto_eq
  {r k : Nat}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  ∃ rate : Real, Tendsto (fun m : Nat => Real.log (fkRectCriticalReducedZ (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds rate) := by
-- proof
  apply StatMech.FrontierD.exists_fkRectFixedChargeVerticalFamily_criticalReducedZ_log_div_height_tendsto r k hq

/--
[fkRectFixedChargeVerticalFamily_arrowPartition_log_div_height_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAllSectorVerticalRate.lean)
-/
@[path]
private lemma fkRectFixedChargeVerticalFamily_arrowPartition_log_div_height_tendsto_eq
  {r k : Nat}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  Tendsto (fun m : Nat => Real.log (sixVertexTorusArrowPartitionSum (fkRectFixedChargeVerticalFamily r k m).medialTorus (fkQgt4SixVertexWeight q)) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (Real.log (sixVertexWidthTopEigenvalue (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)))) := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeVerticalFamily_arrowPartition_log_div_height_tendsto r k hq

/--
[fkRectFixedChargeVerticalFamily_allSector_negLog_div_height_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAllSectorVerticalRate.lean)
-/
@[path]
private lemma fkRectFixedChargeVerticalFamily_allSector_negLog_div_height_eq_eq
  {r k m : Nat}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  -Real.log (fkRectAllSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height = Real.log (fkRectCriticalReducedZ (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height - Real.log (sixVertexTorusArrowPartitionSum (fkRectFixedChargeVerticalFamily r k m).medialTorus (fkQgt4SixVertexWeight q)) / (fkRectFixedChargeVerticalFamily r k m).height - ((fkRectFixedChargeVerticalFamily r k m).width : Real) * Real.log (Real.sqrt q) := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeVerticalFamily_allSector_negLog_div_height_eq r k m hq

/--
[exists_fkRectAllSectorNormalization_vertical_negLogRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAllSectorVerticalRate.lean)
-/
@[path]
private lemma exists_fkRectAllSectorNormalization_vertical_negLogRate_eq
  {r k : Nat}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  ∃ rate : Real, Tendsto (fun m : Nat => -Real.log (fkRectAllSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds rate) := by
-- proof
  apply StatMech.FrontierD.exists_fkRectAllSectorNormalization_vertical_negLogRate r k hq

/--
[fkRectAllSectorNormalization_vertical_negLog_tendsto_rate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAllSectorVerticalRate.lean)
-/
@[path]
private lemma fkRectAllSectorNormalization_vertical_negLog_tendsto_rate_eq
  {q : Real}
  {r k : Nat}
-- given
  (hq : 4 < q) :
-- imply
  Tendsto (fun m : Nat => -Real.log (fkRectAllSectorNormalization (fkRectFixedChargeVerticalFamily r k m) q) / (fkRectFixedChargeVerticalFamily r k m).height) atTop (nhds (fkRectAllSectorNormalizationVerticalRate hq r k)) := by
-- proof
  apply StatMech.FrontierD.fkRectAllSectorNormalization_vertical_negLog_tendsto_rate hq r k


-- created on 2026-10-23
