import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[phb_doubleDualShift_latAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_doubleDualShift_latAdj_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj (phb_doubleDualShift x) (phb_doubleDualShift y) ↔ (hypercubicLattice 2).Adj x y := by
-- proof
  apply StatMech.Lattice.phb_doubleDualShift_latAdj

/--
[phb_sharedPrimalEdge_shift_eq_flankFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_sharedPrimalEdge_shift_eq_flankFaces_eq
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  sharedPrimalEdge (phb_doubleDualShift x) (phb_doubleDualShift y) = flankFaces x y := by
-- proof
  apply StatMech.Lattice.phb_sharedPrimalEdge_shift_eq_flankFaces hxy

/--
[phb_flankFaces_mem_faceBoundaryGraph_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_flankFaces_mem_faceBoundaryGraph_iff_eq
  {K : Set (Site 2)}
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  flankFaces x y ∈ (faceBoundaryGraph K).edgeSet ↔ bdEdge K s(x, y) := by
-- proof
  apply StatMech.Lattice.phb_flankFaces_mem_faceBoundaryGraph_iff hxy

/--
[phb_doubleDual_component_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_doubleDual_component_card_eq
  {K : Set (Site 2)} :
-- imply
  Nat.card (whb_faceRegion (faceBoundaryGraph K)).ConnectedComponent = Nat.card (latticeMinusBarrier K).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.phb_doubleDual_component_card K

/--
[phb_faceBoundaryGraph_support_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_faceBoundaryGraph_support_finite_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  (faceBoundaryGraph K).support.Finite := by
-- proof
  apply StatMech.Lattice.phb_faceBoundaryGraph_support_finite K hK

/--
[phb_mem_boundarySupport_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_mem_boundarySupport_iff_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (hK : K.Finite) :
-- imply
  f ∈ phb_boundarySupport K hK ↔ f ∈ (faceBoundaryGraph K).support := by
-- proof
  apply StatMech.Lattice.phb_mem_boundarySupport_iff K hK f

/--
[phb_imageGraph_planarBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_imageGraph_planarBoundary_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  imageGraph (phb_planarBoundary K hK) = faceBoundaryGraph K := by
-- proof
  apply StatMech.Lattice.phb_imageGraph_planarBoundary K hK

/--
[phb_two_le_degree_planarBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_two_le_degree_planarBoundary_eq
  {K : Set (Site 2)}
  [Fintype (phb_planarBoundary K hK).V]
  [DecidableRel (phb_planarBoundary K hK).G.Adj]
  {v : (phb_planarBoundary K hK).V}
-- given
  (hK : K.Finite) :
-- imply
  2 ≤ (phb_planarBoundary K hK).G.degree v := by
-- proof
  apply StatMech.Lattice.phb_two_le_degree_planarBoundary K hK v

/--
[phb_card_vertices_le_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_card_vertices_le_edges_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  Nat.card (phb_planarBoundary K hK).V ≤ (phb_planarBoundary K hK).G.edgeSet.ncard := by
-- proof
  apply StatMech.Lattice.phb_card_vertices_le_edges K hK

/--
[faceBoundaryConnected_of_connected_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma faceBoundaryConnected_of_connected_complement_eq
  {K : Set (Site 2)}
  {x y : Site 2}
-- given
  (hK : K.Finite)
  (hx : x ∈ K)
  (hy : y ∉ K)
  (hin : ∀ a b : Site 2, a ∈ K → b ∈ K → (latticeMinusBarrier K).Reachable a b)
  (hout : ∀ a b : Site 2, a ∉ K → b ∉ K → (latticeMinusBarrier K).Reachable a b) :
-- imply
  FaceBoundaryConnected K (phb_boundarySupport K hK) := by
-- proof
  apply StatMech.Lattice.faceBoundaryConnected_of_connected_complement K hK hx hy hin hout

/--
[phb_boundary_nullity_one_of_connected_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_boundary_nullity_one_of_connected_complement_eq
  {K : Set (Site 2)}
  {x y : Site 2}
-- given
  (hK : K.Finite)
  (hx : x ∈ K)
  (hy : y ∉ K)
  (hin : ∀ a b : Site 2, a ∈ K → b ∈ K → (latticeMinusBarrier K).Reachable a b)
  (hout : ∀ a b : Site 2, a ∉ K → b ∉ K → (latticeMinusBarrier K).Reachable a b) :
-- imply
  nullity (phb_planarBoundary K hK).G = 1 := by
-- proof
  apply StatMech.Lattice.phb_boundary_nullity_one_of_connected_complement K hK hx hy hin hout

/--
[faceBoundaryGraph_degree_eq_two_of_connected_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma faceBoundaryGraph_degree_eq_two_of_connected_complement_eq
  {K : Set (Site 2)}
  {x y f : Site 2}
-- given
  (hK : K.Finite)
  (hx : x ∈ K)
  (hy : y ∉ K)
  (hin : ∀ a b : Site 2, a ∈ K → b ∈ K → (latticeMinusBarrier K).Reachable a b)
  (hout : ∀ a b : Site 2, a ∉ K → b ∉ K → (latticeMinusBarrier K).Reachable a b)
  (hf : f ∈ (faceBoundaryGraph K).support) :
-- imply
  (faceBoundaryGraph K).degree f = 2 := by
-- proof
  apply StatMech.Lattice.faceBoundaryGraph_degree_eq_two_of_connected_complement K hK hx hy hin hout hf

/--
[phb_planarBoundary_isCycles_of_connected_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean)
-/
@[path]
private lemma phb_planarBoundary_isCycles_of_connected_complement_eq
  {K : Set (Site 2)}
  {x y : Site 2}
-- given
  (hK : K.Finite)
  (hx : x ∈ K)
  (hy : y ∉ K)
  (hin : ∀ a b : Site 2, a ∈ K → b ∈ K → (latticeMinusBarrier K).Reachable a b)
  (hout : ∀ a b : Site 2, a ∉ K → b ∉ K → (latticeMinusBarrier K).Reachable a b) :
-- imply
  (phb_planarBoundary K hK).G.IsCycles := by
-- proof
  apply StatMech.Lattice.phb_planarBoundary_isCycles_of_connected_complement K hK hx hy hin hout


-- created on 2026-10-23
