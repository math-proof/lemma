import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wpjplanarjordan
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[wpj_offSupport_edge_not_walkEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean)
-/
@[path]
private lemma wpj_offSupport_edge_not_walkEdge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hu : u ∉ Vc.support) :
-- imply
  s(u, v) ∉ Vc.edges := by
-- proof
  apply StatMech.Lattice.wpj_offSupport_edge_not_walkEdge Vc hu

/--
[wpj_face_adj_of_offSupport_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean)
-/
@[path]
private lemma wpj_face_adj_of_offSupport_wall_eq
  {G : SimpleGraph (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {f g u v : Site 2}
-- given
  (hGV : G.edgeSet ⊆ {e | e ∈ Vc.edges})
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(u, v))
  (hu : u ∉ Vc.support) :
-- imply
  (whb_faceRegion G).Adj f g := by
-- proof
  apply StatMech.Lattice.wpj_face_adj_of_offSupport_wall G Vc hGV hfg hshared hu

/--
[wpj_barrier_separates_inside_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean)
-/
@[path]
private lemma wpj_barrier_separates_inside_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ jec_leftRegion Vc)
  (hy : y ∉ jec_leftRegion Vc) :
-- imply
  ¬ Even (crossCount (jec_leftRegion Vc) w) := by
-- proof
  apply StatMech.Lattice.wpj_barrier_separates_inside_outside Vc hx hy w

/--
[wpj_latticeMinusBarrier_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean)
-/
@[path]
private lemma wpj_latticeMinusBarrier_separates_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∈ jec_leftRegion Vc)
  (hy : y ∉ jec_leftRegion Vc) :
-- imply
  ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.wpj_latticeMinusBarrier_separates Vc hx hy

/--
[wpj_winding_separation_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean)
-/
@[path]
private lemma wpj_winding_separation_of_bridge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wpj_PlaneDualityBridge Vc) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.wpj_winding_separation_of_bridge Vc h

/--
[wpj_offComplJordanRegion_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean)
-/
@[path]
private lemma wpj_offComplJordanRegion_of_bridge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wpj_PlaneDualityBridge Vc) :
-- imply
  fcb_OffComplJordanRegion Vc := by
-- proof
  apply StatMech.Lattice.wpj_offComplJordanRegion_of_bridge Vc h

/--
[wpj_jed_faithful_dual_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean)
-/
@[path]
private lemma wpj_jed_faithful_dual_count_eq
  {P : PlanarZ2Subgraph} :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.wpj_jed_faithful_dual_count P

/--
[wpj_support_site_not_offSupport_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean)
-/
@[path]
private lemma wpj_support_site_not_offSupport_vertex_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {s : Site 2}
-- given
  (hs : s ∈ Vc.support) :
-- imply
  ¬ (s ∈ {z : Site 2 | z ∉ Vc.support}) := by
-- proof
  apply StatMech.Lattice.wpj_support_site_not_offSupport_vertex Vc hs

/--
[wpj_basepoint_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean)
-/
@[path]
private lemma wpj_basepoint_mem_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  a ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.wpj_basepoint_mem_support Vc


-- created on 2026-10-23
