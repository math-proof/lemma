import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[bdEdge_eq_edgeStraddles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma bdEdge_eq_edgeStraddles_eq
  {K : Set (Site 2)}
  {e : Sym2 (Site 2)} :
-- imply
  bdEdge K e ↔ edgeStraddles K e := by
-- proof
  apply StatMech.Lattice.bdEdge_eq_edgeStraddles K e

/--
[faceBoundaryGraph_adj_iff_boundaryEdgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma faceBoundaryGraph_adj_iff_boundaryEdgeSet_eq
  {K : Set (Site 2)}
  {f g : Site 2} :
-- imply
  (faceBoundaryGraph K).Adj f g ↔ (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g ∈ boundaryEdgeSet K := by
-- proof
  apply StatMech.Lattice.faceBoundaryGraph_adj_iff_boundaryEdgeSet K f g

/--
[dualFace_incident_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma dualFace_incident_even_eq
  {K : Set (Site 2)}
  {f : Site 2} :
-- imply
  Even ((faceBoundaryGraph K).degree f) := by
-- proof
  apply StatMech.Lattice.dualFace_incident_even K f

/--
[dualFace_boundaryEdge_count_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma dualFace_boundaryEdge_count_even_eq
  {K : Set (Site 2)}
  {f : Site 2} :
-- imply
  Even ((faceBoundaryGraph K).neighborFinset f).card := by
-- proof
  apply StatMech.Lattice.dualFace_boundaryEdge_count_even K f

/--
[connCluster_dualFace_incident_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma connCluster_dualFace_incident_even_eq
  {K : Finset (Site 2)}
  {f : Site 2}
-- given
  (_hK : IsConnectedCluster K) :
-- imply
  Even ((faceBoundaryGraph (↑K : Set (Site 2))).degree f) := by
-- proof
  apply StatMech.Lattice.connCluster_dualFace_incident_even _hK f

/--
[connCluster_contour_edge_on_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma connCluster_contour_edge_on_cycle_eq
  {K : Finset (Site 2)}
  {f g : Site 2}
-- given
  (_hK : IsConnectedCluster K)
  (hadj : (faceBoundaryGraph (↑K : Set (Site 2))).Adj f g) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u), c.IsCycle ∧ s(f, g) ∈ c.edges := by
-- proof
  apply StatMech.Lattice.connCluster_contour_edge_on_cycle _hK hadj

/--
[faceBoundaryGraph_eq_of_boundaryEdgeSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma faceBoundaryGraph_eq_of_boundaryEdgeSet_eq_eq
  {K₁ K₂ : Set (Site 2)}
-- given
  (h : boundaryEdgeSet K₁ = boundaryEdgeSet K₂) :
-- imply
  faceBoundaryGraph K₁ = faceBoundaryGraph K₂ := by
-- proof
  apply StatMech.Lattice.faceBoundaryGraph_eq_of_boundaryEdgeSet_eq h

/--
[connCluster_evenContour_and_recovery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma connCluster_evenContour_and_recovery_eq
  {K : Finset (Site 2)}
-- given
  (hK : IsConnectedCluster K) :
-- imply
  (∀ f : Site 2, Even ((faceBoundaryGraph (↑K : Set (Site 2))).degree f)) ∧ (∀ x : Site 2, x ∈ (↑K : Set (Site 2)) ↔ (latticeMinusBoundary (↑K : Set (Site 2))).Reachable (origin 2) x) := by
-- proof
  apply StatMech.Lattice.connCluster_evenContour_and_recovery hK

/--
[singletonOrigin_isConnectedCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma singletonOrigin_isConnectedCluster_eq :
-- imply
  IsConnectedCluster ({origin 2} : Finset (Site 2)) := by
-- proof
  apply StatMech.Lattice.singletonOrigin_isConnectedCluster

/--
[origin_eq_zerozero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma origin_eq_zerozero_eq :
-- imply
  (origin 2) = (![0, 0] : Site 2) := by
-- proof
  apply StatMech.Lattice.origin_eq_zerozero

/--
[origin_mem_singleton_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma origin_mem_singleton_coe_eq :
-- imply
  (![0, 0] : Site 2) ∈ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.origin_mem_singleton_coe

/--
[one_zero_notMem_singleton_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma one_zero_notMem_singleton_coe_eq :
-- imply
  (![1, 0] : Site 2) ∉ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.one_zero_notMem_singleton_coe

/--
[singleton_origin_dualFace_incident_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsEulerParity.lean)
-/
@[path]
private lemma singleton_origin_dualFace_incident_even_eq :
-- imply
  (∀ f : Site 2, Even ((faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).degree f)) ∧ ∃ f g : Site 2, (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj f g := by
-- proof
  apply StatMech.Lattice.singleton_origin_dualFace_incident_even


-- created on 2026-10-23
