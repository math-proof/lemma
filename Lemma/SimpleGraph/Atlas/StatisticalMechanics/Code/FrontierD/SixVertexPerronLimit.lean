import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronLimit
open Finset Filter Matrix Topology StatMech StatMech.FrontierD


/--
[sixVertexSectorTop_div_le_normalizedMaxRowSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronLimit.lean)
-/
@[path]
private lemma sixVertexSectorTop_div_le_normalizedMaxRowSum_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : n ≤ N)
  (hc : 0 < c)
  (hden : 0 < (c ^ 2 - 2) ^ n) :
-- imply
  sixVertexSectorTopEigenvalue N n hn c / (c ^ 2 - 2) ^ n ≤ sixVertexSectorTransferNormalizedMaxRowSum N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTop_div_le_normalizedMaxRowSum hn hc hden

/--
[sixVertexSectorTransfer_entry_le_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronLimit.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_entry_le_top_eq
  {N n : Nat}
  {c : Real}
  {x y : SixVertexSector N n}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  sixVertexSectorTransfer N n c x y ≤ sixVertexSectorTopEigenvalue N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_entry_le_top hn hc x y

/--
[tendsto_sixVertexSectorTransferNormalizedMaxRowSum_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexSectorTransferNormalizedMaxRowSum_half_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  Tendsto (sixVertexSectorTransferNormalizedMaxRowSum N n (by omega)) atTop (nhds 1) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexSectorTransferNormalizedMaxRowSum_half hn hhalf

/--
[tendsto_sixVertexSectorTop_normalized_atTop_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronLimit.lean)
-/
@[path]
private lemma tendsto_sixVertexSectorTop_normalized_atTop_half_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  Tendsto (fun c => sixVertexSectorTopEigenvalue N n (by omega) c / (c ^ 2 - 2) ^ n) atTop (nhds 1) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexSectorTop_normalized_atTop_half hn hhalf


-- created on 2026-10-23
