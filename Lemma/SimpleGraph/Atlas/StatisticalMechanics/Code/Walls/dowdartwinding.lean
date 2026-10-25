import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.dowdartwinding
open Set SimpleGraph StatMech StatMech.Walls


/--
[dow_odd_count_iff_mem_of_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dowdartwinding.lean)
-/
@[path]
private lemma dow_odd_count_iff_mem_of_nodup_eq
  [DecidableEq α]
  {l : List α}
  {e : α}
-- given
  (hnd : l.Nodup) :
-- imply
  Odd (l.count e) ↔ e ∈ l := by
-- proof
  apply StatMech.Walls.dow_odd_count_iff_mem_of_nodup hnd e

/--
[dow_walk_odd_count_iff_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dowdartwinding.lean)
-/
@[path]
private lemma dow_walk_odd_count_iff_mem_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {e : Sym2 (Site 2)}
-- given
  (hnd : Vc.edges.Nodup) :
-- imply
  Odd (Vc.edges.count e) ↔ e ∈ Vc.edges := by
-- proof
  apply StatMech.Walls.dow_walk_odd_count_iff_mem Vc hnd e

/--
[dow_bridge_iff_crossEdge_mem_iff_shared_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dowdartwinding.lean)
-/
@[path]
private lemma dow_bridge_iff_crossEdge_mem_iff_shared_mem_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hnd : Vc.edges.Nodup) :
-- imply
  rpc_CrossEdgeOddIffOnWalk Vc ↔ (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (rpc_crossEdge u v ∈ Vc.edges ↔ s(u, v) ∈ Vc.edges)) := by
-- proof
  apply StatMech.Walls.dow_bridge_iff_crossEdge_mem_iff_shared_mem Vc hnd

/--
[dow_bridge_iff_bdEdge_shared_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dowdartwinding.lean)
-/
@[path]
private lemma dow_bridge_iff_bdEdge_shared_mem_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  rpc_CrossEdgeOddIffOnWalk Vc ↔ (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (bdEdge (jec_leftRegion Vc) s(u, v) ↔ s(u, v) ∈ Vc.edges)) := by
-- proof
  apply StatMech.Walls.dow_bridge_iff_bdEdge_shared_mem Vc

/--
[dow_bdEdge_meets_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dowdartwinding.lean)
-/
@[path]
private lemma dow_bdEdge_meets_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Walls.dow_bdEdge_meets_support Vc hadj hbd

/--
[dow_off_support_not_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dowdartwinding.lean)
-/
@[path]
private lemma dow_off_support_not_bdEdge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  ¬ bdEdge (jec_leftRegion Vc) s(u, v) := by
-- proof
  apply StatMech.Walls.dow_off_support_not_bdEdge Vc hadj hu hv

/--
[dow_bridge_iff_hardGap_and_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dowdartwinding.lean)
-/
@[path]
private lemma dow_bridge_iff_hardGap_and_reverse_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (_hnd : Vc.edges.Nodup) :
-- imply
  rpc_CrossEdgeOddIffOnWalk Vc ↔ (jbw_hard_gap Vc ∧ ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges) := by
-- proof
  apply StatMech.Walls.dow_bridge_iff_hardGap_and_reverse Vc _hnd

/--
[dow_bridge_of_hardGap_and_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dowdartwinding.lean)
-/
@[path]
private lemma dow_bridge_of_hardGap_and_reverse_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hnd : Vc.edges.Nodup)
  (hhard : jbw_hard_gap Vc)
  (hrev : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges) :
-- imply
  rpc_CrossEdgeOddIffOnWalk Vc := by
-- proof
  apply StatMech.Walls.dow_bridge_of_hardGap_and_reverse Vc hnd hhard hrev

/--
[dow_primalWalkLeftRegionMatch_of_hardGap_and_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dowdartwinding.lean)
-/
@[path]
private lemma dow_primalWalkLeftRegionMatch_of_hardGap_and_reverse_eq
-- given
  (hnd : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), Vc.edges.Nodup)
  (hhard : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), jbw_hard_gap Vc)
  (hrev : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2}, (hypercubicLattice 2).Adj u v → bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges) :
-- imply
  kwc_PrimalWalkLeftRegionMatch := by
-- proof
  apply StatMech.Walls.dow_primalWalkLeftRegionMatch_of_hardGap_and_reverse hnd hhard hrev

/--
[dow_unitSquare_bridgeBody](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dowdartwinding.lean)
-/
@[path]
private lemma dow_unitSquare_bridgeBody_eq :
-- imply
  Odd (wwit_unitSquareLoop.edges.count (rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2))) ↔ bdEdge (jec_leftRegion wwit_unitSquareLoop) s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
-- proof
  apply StatMech.Walls.dow_unitSquare_bridgeBody


-- created on 2026-10-23
