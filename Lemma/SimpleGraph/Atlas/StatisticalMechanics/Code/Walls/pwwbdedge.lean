import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.pwwbdedge.Part3
open Set SimpleGraph StatMech StatMech.Walls


/--
[pww_a_adj_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean)
-/
@[path]
private lemma pww_a_adj_b_eq :
-- imply
  (hypercubicLattice 2).Adj pww_a pww_b := by
-- proof
  apply StatMech.Walls.pww_a_adj_b

/--
[pww_backForth_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean)
-/
@[path]
private lemma pww_backForth_edge_mem_eq :
-- imply
  s(pww_a, pww_b) ∈ pww_backForth.edges.toFinset := by
-- proof
  apply StatMech.Walls.pww_backForth_edge_mem

/--
[pww_backForth_rayCount_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean)
-/
@[path]
private lemma pww_backForth_rayCount_even_eq
  {z : Site 2} :
-- imply
  Even (jec_rayCount z pww_backForth) := by
-- proof
  apply StatMech.Walls.pww_backForth_rayCount_even z

/--
[pww_backForth_leftRegion_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean)
-/
@[path]
private lemma pww_backForth_leftRegion_empty_eq :
-- imply
  jec_leftRegion pww_backForth = (∅ : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.pww_backForth_leftRegion_empty

/--
[pww_backForth_not_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean)
-/
@[path]
private lemma pww_backForth_not_bdEdge_eq :
-- imply
  ¬ bdEdge (jec_leftRegion pww_backForth) s(pww_a, pww_b) := by
-- proof
  apply StatMech.Walls.pww_backForth_not_bdEdge

/--
[pww_PrimalWalkLeftRegionMatch_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean)
-/
@[path]
private lemma pww_PrimalWalkLeftRegionMatch_false_eq :
-- imply
  ¬ kwc_PrimalWalkLeftRegionMatch := by
-- proof
  apply StatMech.Walls.pww_PrimalWalkLeftRegionMatch_false

/--
[pww_bdEdge_endpoint_on_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean)
-/
@[path]
private lemma pww_bdEdge_endpoint_on_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Walls.pww_bdEdge_endpoint_on_support Vc hadj hbd

/--
[pww_bdEdge_iff_flip_and_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean)
-/
@[path]
private lemma pww_bdEdge_iff_flip_and_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  bdEdge (jec_leftRegion Vc) s(u, v) ↔ ((u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) ∧ (u ∈ Vc.support ∨ v ∈ Vc.support)) := by
-- proof
  apply StatMech.Walls.pww_bdEdge_iff_flip_and_support Vc hadj

/--
[pww_leftRegionMatch_of_cycle_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean)
-/
@[path]
private lemma pww_leftRegionMatch_of_cycle_forward_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hcrux : pww_ForwardCrux Vc)
  (hback : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges.toFinset)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v) := by
-- proof
  apply StatMech.Walls.pww_leftRegionMatch_of_cycle_forward Vc hcrux hback hadj

/--
[pww_leftRegionMatch_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean)
-/
@[path]
private lemma pww_leftRegionMatch_nil_eq
  {a : Site 2}
  {u v : Site 2}
-- given
  (_hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  (s(u, v) ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a).edges.toFinset ↔ bdEdge (jec_leftRegion (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a)) s(u, v)) := by
-- proof
  apply StatMech.Walls.pww_leftRegionMatch_nil _hadj


-- created on 2026-10-23
