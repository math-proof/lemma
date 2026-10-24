import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy
open Finset Matrix Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexWidthSectorIndex_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean)
-/
@[path]
private lemma sixVertexWidthSectorIndex_le_eq
  {N : ℕ}
  {n : Fin (N + 1)} :
-- imply
  n.val ≤ N := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthSectorIndex_le N n

/--
[sixVertexWidthSectorTopEigenvalue_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean)
-/
@[path]
private lemma sixVertexWidthSectorTopEigenvalue_le_eq
  {N : ℕ}
  {c : ℝ}
  {n : Fin (N + 1)} :
-- imply
  sixVertexWidthSectorTopEigenvalue N c n ≤ sixVertexWidthTopEigenvalue N c := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthSectorTopEigenvalue_le N c n

/--
[sixVertexWidthTopEigenvalue_exists_sector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean)
-/
@[path]
private lemma sixVertexWidthTopEigenvalue_exists_sector_eq
  {N : ℕ}
  {c : ℝ} :
-- imply
  ∃ n : Fin (N + 1), sixVertexWidthSectorTopEigenvalue N c n = sixVertexWidthTopEigenvalue N c := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthTopEigenvalue_exists_sector N c

/--
[sixVertexWidthTopEigenvalue_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean)
-/
@[path]
private lemma sixVertexWidthTopEigenvalue_pos_eq
  {N : ℕ}
  {c : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  0 < sixVertexWidthTopEigenvalue N c := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthTopEigenvalue_pos N hc

/--
[sixVertexFixedWidthPartitionSum_eq_periodicRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean)
-/
@[path]
private lemma sixVertexFixedWidthPartitionSum_eq_periodicRows_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hM : 0 < M) :
-- imply
  sixVertexFixedWidthPartitionSum N M c = sixVertexPeriodicRowPartitionSum N M hM c := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedWidthPartitionSum_eq_periodicRows N M hM c

/--
[sixVertexFixedWidthPartitionSum_eq_sum_sector_traces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean)
-/
@[path]
private lemma sixVertexFixedWidthPartitionSum_eq_sum_sector_traces_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hM : 0 < M) :
-- imply
  sixVertexFixedWidthPartitionSum N M c = ∑ n : Fin (N + 1), Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedWidthPartitionSum_eq_sum_sector_traces N M hM c

/--
[sixVertexFixedWidthPartitionSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean)
-/
@[path]
private lemma sixVertexFixedWidthPartitionSum_pos_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hM : 0 < M)
  (hc : 0 < c) :
-- imply
  0 < sixVertexFixedWidthPartitionSum N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedWidthPartitionSum_pos N M hM hc

/--
[sixVertexWidthMaxSectorCount_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean)
-/
@[path]
private lemma sixVertexWidthMaxSectorCount_pos_eq
  {N : ℕ}
  {c : ℝ} :
-- imply
  0 < sixVertexWidthMaxSectorCount N c := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthMaxSectorCount_pos N c

/--
[sixVertexFixedWidthPartitionSum_div_top_pow_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean)
-/
@[path]
private lemma sixVertexFixedWidthPartitionSum_div_top_pow_tendsto_eq
  {N : ℕ}
  {c : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (fun M : ℕ => sixVertexFixedWidthPartitionSum N M c / sixVertexWidthTopEigenvalue N c ^ M) atTop (nhds (sixVertexWidthMaxSectorCount N c)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedWidthPartitionSum_div_top_pow_tendsto N hc

/--
[sixVertexFixedWidth_log_partition_div_height_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean)
-/
@[path]
private lemma sixVertexFixedWidth_log_partition_div_height_tendsto_eq
  {N : ℕ}
  {c : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  Tendsto (fun M : ℕ => Real.log (sixVertexFixedWidthPartitionSum N M c) / (M : ℝ)) atTop (nhds (Real.log (sixVertexWidthTopEigenvalue N c))) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedWidth_log_partition_div_height_tendsto N hc


-- created on 2026-10-23
