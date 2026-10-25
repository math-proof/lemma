import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
open Set SimpleGraph StatMech StatMech.Walls


/--
[rpc_hCrossEdge_isRayEdge_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_hCrossEdge_isRayEdge_left_eq
  {u : Site 2} :
-- imply
  ¬ jec_rayEdge u (rpc_hCrossEdge u) := by
-- proof
  apply StatMech.Walls.rpc_hCrossEdge_isRayEdge_left u

/--
[rpc_hCrossEdge_isRayEdge_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_hCrossEdge_isRayEdge_right_eq
  {u v : Site 2}
-- given
  (h0 : v 0 = u 0 + 1)
  (h1 : v 1 = u 1) :
-- imply
  jec_rayEdge v (rpc_hCrossEdge u) := by
-- proof
  apply StatMech.Walls.rpc_hCrossEdge_isRayEdge_right u v h0 h1

/--
[rpc_rayEdge_horizontalStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_rayEdge_horizontalStep_eq
  {u v : Site 2}
  {p q : Site 2}
-- given
  (h0 : v 0 = u 0 + 1)
  (h1 : v 1 = u 1)
  (_hadj : (hypercubicLattice 2).Adj p q) :
-- imply
  jec_rayEdge v s(p, q) ↔ (jec_rayEdge u s(p, q) ∨ s(p, q) = rpc_hCrossEdge u) := by
-- proof
  apply StatMech.Walls.rpc_rayEdge_horizontalStep u v h0 h1 _hadj

/--
[rpc_rayCount_edges_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_rayCount_edges_split_eq
  {u v : Site 2}
  {l : List (Sym2 (Site 2))}
-- given
  (h0 : v 0 = u 0 + 1)
  (h1 : v 1 = u 1)
  (hl : ∀ e ∈ l, ∃ p q, e = s(p, q) ∧ (hypercubicLattice 2).Adj p q) :
-- imply
  l.countP (fun e => decide (jec_rayEdge v e)) = l.countP (fun e => decide (jec_rayEdge u e)) + l.count (rpc_hCrossEdge u) := by
-- proof
  apply StatMech.Walls.rpc_rayCount_edges_split u v h0 h1 l hl

/--
[rpc_rayCount_horizontalStep_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_rayCount_horizontalStep_diff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (h0 : v 0 = u 0 + 1)
  (h1 : v 1 = u 1) :
-- imply
  jec_rayCount v Vc = jec_rayCount u Vc + Vc.edges.count (rpc_hCrossEdge u) := by
-- proof
  apply StatMech.Walls.rpc_rayCount_horizontalStep_diff Vc u v h0 h1

/--
[rpc_horizontalFlip_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_horizontalFlip_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (h0 : v 0 = u 0 + 1)
  (h1 : v 1 = u 1) :
-- imply
  (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) ↔ Odd (Vc.edges.count (rpc_hCrossEdge u)) := by
-- proof
  apply StatMech.Walls.rpc_horizontalFlip_iff Vc u v h0 h1

/--
[rpc_vCrossEdge_isWallEdge_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_vCrossEdge_isWallEdge_left_eq
  {u : Site 2} :
-- imply
  ¬ jec_wallEdge u (rpc_vCrossEdge u) := by
-- proof
  apply StatMech.Walls.rpc_vCrossEdge_isWallEdge_left u

/--
[rpc_wallEdge_verticalStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_wallEdge_verticalStep_eq
  {u v : Site 2}
  {p q : Site 2}
-- given
  (h0 : v 0 = u 0)
  (h1 : v 1 = u 1 + 1)
  (_hadj : (hypercubicLattice 2).Adj p q) :
-- imply
  jec_wallEdge v s(p, q) ↔ (jec_wallEdge u s(p, q) ∨ s(p, q) = rpc_vCrossEdge u) := by
-- proof
  apply StatMech.Walls.rpc_wallEdge_verticalStep u v h0 h1 _hadj

/--
[rpc_wallCount_edges_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_wallCount_edges_split_eq
  {u v : Site 2}
  {l : List (Sym2 (Site 2))}
-- given
  (h0 : v 0 = u 0)
  (h1 : v 1 = u 1 + 1)
  (hl : ∀ e ∈ l, ∃ p q, e = s(p, q) ∧ (hypercubicLattice 2).Adj p q) :
-- imply
  l.countP (fun e => decide (jec_wallEdge v e)) = l.countP (fun e => decide (jec_wallEdge u e)) + l.count (rpc_vCrossEdge u) := by
-- proof
  apply StatMech.Walls.rpc_wallCount_edges_split u v h0 h1 l hl

/--
[rpc_wallCount_verticalStep_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_wallCount_verticalStep_diff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (h0 : v 0 = u 0)
  (h1 : v 1 = u 1 + 1) :
-- imply
  jec_wallCount v Vc = jec_wallCount u Vc + Vc.edges.count (rpc_vCrossEdge u) := by
-- proof
  apply StatMech.Walls.rpc_wallCount_verticalStep_diff Vc u v h0 h1

/--
[rpc_verticalFlip_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_verticalFlip_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (h0 : v 0 = u 0)
  (h1 : v 1 = u 1 + 1) :
-- imply
  (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) ↔ Odd (Vc.edges.count (rpc_vCrossEdge u)) := by
-- proof
  apply StatMech.Walls.rpc_verticalFlip_iff Vc u v h0 h1

/--
[rpc_crossFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_crossFlip_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  bdEdge (jec_leftRegion Vc) s(u, v) ↔ Odd (Vc.edges.count (rpc_crossEdge u v)) := by
-- proof
  apply StatMech.Walls.rpc_crossFlip Vc hadj

/--
[rpc_leftRegion_bdEdge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_leftRegion_bdEdge_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hbridge : rpc_CrossEdgeOddIffOnWalk Vc)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  bdEdge (jec_leftRegion Vc) s(u, v) ↔ s(u, v) ∈ Vc.edges := by
-- proof
  apply StatMech.Walls.rpc_leftRegion_bdEdge_iff Vc hbridge hadj

/--
[rpc_primalWalkLeftRegionMatch_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_primalWalkLeftRegionMatch_of_bridge_eq
-- given
  (hbridge : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), rpc_CrossEdgeOddIffOnWalk Vc) :
-- imply
  kwc_PrimalWalkLeftRegionMatch := by
-- proof
  apply StatMech.Walls.rpc_primalWalkLeftRegionMatch_of_bridge hbridge

/--
[rpc_unitSquare_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_unitSquare_flip_eq :
-- imply
  bdEdge (jec_leftRegion wwit_unitSquareLoop) s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
-- proof
  apply StatMech.Walls.rpc_unitSquare_flip

/--
[rpc_unitSquare_crossEdge_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean)
-/
@[path]
private lemma rpc_unitSquare_crossEdge_odd_eq :
-- imply
  Odd (wwit_unitSquareLoop.edges.count (rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2))) := by
-- proof
  apply StatMech.Walls.rpc_unitSquare_crossEdge_odd


-- created on 2026-10-23
