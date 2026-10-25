import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.ceosimplecycle
open Set SimpleGraph StatMech StatMech.Walls


/--
[ceo_shiftSquare_edges_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ceosimplecycle.lean)
-/
@[path]
private lemma ceo_shiftSquare_edges_nodup_eq :
-- imply
  ceo_shiftSquare.edges.Nodup := by
-- proof
  apply StatMech.Walls.ceo_shiftSquare_edges_nodup

/--
[ceo_uv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ceosimplecycle.lean)
-/
@[path]
private lemma ceo_uv_adj_eq :
-- imply
  (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Walls.ceo_uv_adj

/--
[ceo_shiftSquare_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ceosimplecycle.lean)
-/
@[path]
private lemma ceo_shiftSquare_edge_mem_eq :
-- imply
  s((![0, 1] : Site 2), (![1, 1] : Site 2)) ∈ ceo_shiftSquare.edges := by
-- proof
  apply StatMech.Walls.ceo_shiftSquare_edge_mem

/--
[ceo_shiftSquare_crossEdge_count_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ceosimplecycle.lean)
-/
@[path]
private lemma ceo_shiftSquare_crossEdge_count_zero_eq :
-- imply
  ceo_shiftSquare.edges.count (rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2)) = 0 := by
-- proof
  apply StatMech.Walls.ceo_shiftSquare_crossEdge_count_zero

/--
[ceo_shiftSquare_residue_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ceosimplecycle.lean)
-/
@[path]
private lemma ceo_shiftSquare_residue_false_eq :
-- imply
  ¬ rpc_CrossEdgeOddIffOnWalk ceo_shiftSquare := by
-- proof
  apply StatMech.Walls.ceo_shiftSquare_residue_false

/--
[ceo_shiftSquare_rayCount_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ceosimplecycle.lean)
-/
@[path]
private lemma ceo_shiftSquare_rayCount_endpoints_eq :
-- imply
  jec_rayCount (![0, 1] : Site 2) ceo_shiftSquare = 0 ∧ jec_rayCount (![1, 1] : Site 2) ceo_shiftSquare = 0 := by
-- proof
  apply StatMech.Walls.ceo_shiftSquare_rayCount_endpoints

/--
[ceo_shiftSquare_inside_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ceosimplecycle.lean)
-/
@[path]
private lemma ceo_shiftSquare_inside_odd_eq :
-- imply
  jec_rayCount (![1, 2] : Site 2) ceo_shiftSquare = 1 := by
-- proof
  apply StatMech.Walls.ceo_shiftSquare_inside_odd

/--
[ceo_shiftSquare_not_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ceosimplecycle.lean)
-/
@[path]
private lemma ceo_shiftSquare_not_bdEdge_eq :
-- imply
  ¬ bdEdge (jec_leftRegion ceo_shiftSquare) s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
-- proof
  apply StatMech.Walls.ceo_shiftSquare_not_bdEdge

/--
[ceo_primalWalkLeftRegionMatch_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ceosimplecycle.lean)
-/
@[path]
private lemma ceo_primalWalkLeftRegionMatch_false_eq :
-- imply
  ¬ kwc_PrimalWalkLeftRegionMatch := by
-- proof
  apply StatMech.Walls.ceo_primalWalkLeftRegionMatch_false


-- created on 2026-10-23
