import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanEnclosure
open Finset Set SimpleGraph StatMech StatMech.Lattice StatMech.Lattice.EvenDegree


/--
[sum_degree_component_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma sum_degree_component_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : G.ConnectedComponent} :
-- imply
  Even (∑ x ∈ C.supp.toFinset, G.degree x) := by
-- proof
  apply StatMech.Lattice.EvenDegree.sum_degree_component_even G C

/--
[degree_deleteEdges_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma degree_deleteEdges_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v w x : V}
-- given
  (hxv : x ≠ v)
  (hxw : x ≠ w) :
-- imply
  (G.deleteEdges {s(v, w)}).degree x = G.degree x := by
-- proof
  apply StatMech.Lattice.EvenDegree.degree_deleteEdges_of_ne G hxv hxw

/--
[degree_deleteEdges_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma degree_deleteEdges_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v w : V}
-- given
  (hadj : G.Adj v w) :
-- imply
  (G.deleteEdges {s(v, w)}).degree v + 1 = G.degree v := by
-- proof
  apply StatMech.Lattice.EvenDegree.degree_deleteEdges_self G hadj

/--
[reachable_deleteEdges_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma reachable_deleteEdges_of_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v w : V}
-- given
  (heven : ∀ x, Even (G.degree x))
  (hadj : G.Adj v w) :
-- imply
  (G.deleteEdges {s(v, w)}).Reachable v w := by
-- proof
  apply StatMech.Lattice.EvenDegree.reachable_deleteEdges_of_even G heven hadj

/--
[exists_cycle_through_edge_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma exists_cycle_through_edge_of_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v w : V}
-- given
  (heven : ∀ x, Even (G.degree x))
  (hadj : G.Adj v w) :
-- imply
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
-- proof
  apply StatMech.Lattice.EvenDegree.exists_cycle_through_edge_of_even G heven hadj

/--
[exists_cycle_through_edge_of_even_of_finite_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma exists_cycle_through_edge_of_even_of_finite_support_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {T : Finset V}
  {v w : V}
-- given
  (hsupp : G.support ⊆ (T : Set V))
  (heven : ∀ x, Even (G.degree x))
  (hadj : G.Adj v w) :
-- imply
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
-- proof
  apply StatMech.Lattice.EvenDegree.exists_cycle_through_edge_of_even_of_finite_support G T hsupp heven hadj

/--
[sharedPrimalEdge_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma sharedPrimalEdge_right_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a, b] ![a + 1, b] = s(faceCorner10 a b, faceCorner11 a b) := by
-- proof
  apply StatMech.Lattice.sharedPrimalEdge_right a b

/--
[sharedPrimalEdge_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma sharedPrimalEdge_left_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a, b] ![a - 1, b] = s(faceCorner00 a b, faceCorner01 a b) := by
-- proof
  apply StatMech.Lattice.sharedPrimalEdge_left a b

/--
[sharedPrimalEdge_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma sharedPrimalEdge_top_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a, b] ![a, b + 1] = s(faceCorner01 a b, faceCorner11 a b) := by
-- proof
  apply StatMech.Lattice.sharedPrimalEdge_top a b

/--
[sharedPrimalEdge_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma sharedPrimalEdge_bottom_eq
  {a b : ℤ} :
-- imply
  sharedPrimalEdge ![a, b] ![a, b - 1] = s(faceCorner00 a b, faceCorner10 a b) := by
-- proof
  apply StatMech.Lattice.sharedPrimalEdge_bottom a b

/--
[bdEdge_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma bdEdge_mk_eq
  {S : Set (Site 2)}
  {x y : Site 2} :
-- imply
  bdEdge S s(x, y) ↔ (x ∈ S ↔ y ∉ S) := by
-- proof
  apply StatMech.Lattice.bdEdge_mk S x y

/--
[bdEdge_iff_bdInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma bdEdge_iff_bdInd_eq
  {S : Set (Site 2)}
  {x y : Site 2} :
-- imply
  bdEdge S s(x, y) ↔ bdInd S x y = 1 := by
-- proof
  apply StatMech.Lattice.bdEdge_iff_bdInd S x y

/--
[sharedPrimalEdge_comm_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma sharedPrimalEdge_comm_of_adj_eq
  {f g : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g) :
-- imply
  sharedPrimalEdge f g = sharedPrimalEdge g f := by
-- proof
  apply StatMech.Lattice.sharedPrimalEdge_comm_of_adj h

/--
[faceBoundaryGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma faceBoundaryGraph_adj_eq
  {S : Set (Site 2)}
  {f g : Site 2} :
-- imply
  (faceBoundaryGraph S).Adj f g ↔ (hypercubicLattice 2).Adj f g ∧ bdEdge S (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Lattice.faceBoundaryGraph_adj S f g

/--
[faceBoundaryGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma faceBoundaryGraph_le_eq
  {S : Set (Site 2)} :
-- imply
  faceBoundaryGraph S ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.faceBoundaryGraph_le S

/--
[latAdj_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma latAdj_right_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
-- proof
  apply StatMech.Lattice.latAdj_right a b

/--
[latAdj_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma latAdj_left_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a - 1, b] := by
-- proof
  apply StatMech.Lattice.latAdj_left a b

/--
[latAdj_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma latAdj_top_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a, b + 1] := by
-- proof
  apply StatMech.Lattice.latAdj_top a b

/--
[latAdj_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma latAdj_bottom_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a, b - 1] := by
-- proof
  apply StatMech.Lattice.latAdj_bottom a b

/--
[candFinset_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma candFinset_face_eq
  {a b : ℤ} :
-- imply
  candFinset 2 ![a, b] = ({![a + 1, b], ![a - 1, b], ![a, b + 1], ![a, b - 1]} : Finset (Site 2)) := by
-- proof
  apply StatMech.Lattice.candFinset_face a b

/--
[neighborFinset_faceBoundaryGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma neighborFinset_faceBoundaryGraph_eq
  {S : Set (Site 2)}
  {f : Site 2} :
-- imply
  (faceBoundaryGraph S).neighborFinset f = (candFinset 2 f).filter (fun g => (faceBoundaryGraph S).Adj f g) := by
-- proof
  apply StatMech.Lattice.neighborFinset_faceBoundaryGraph S f

/--
[degree_faceBoundaryGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma degree_faceBoundaryGraph_eq
  {S : Set (Site 2)}
  {a b : ℤ} :
-- imply
  (faceBoundaryGraph S).degree ![a, b] = faceBoundaryDegree S a b := by
-- proof
  apply StatMech.Lattice.degree_faceBoundaryGraph S a b

/--
[degree_faceBoundaryGraph_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma degree_faceBoundaryGraph_even_eq
  {S : Set (Site 2)}
  {f : Site 2} :
-- imply
  Even ((faceBoundaryGraph S).degree f) := by
-- proof
  apply StatMech.Lattice.degree_faceBoundaryGraph_even S f

/--
[site2_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma site2_eq_eq
  {x y x' y' : ℤ} :
-- imply
  (![x, y] : Site 2) = ![x', y'] ↔ x = x' ∧ y = y' := by
-- proof
  apply StatMech.Lattice.site2_eq x y x' y'

/--
[mem_cornerFaces_of_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma mem_cornerFaces_of_corner_eq
  {a b : ℤ}
  {c : Site 2}
-- given
  (hc : c = ![a, b] ∨ c = ![a + 1, b] ∨ c = ![a + 1, b + 1] ∨ c = ![a, b + 1]) :
-- imply
  (![a, b] : Site 2) ∈ cornerFaces c := by
-- proof
  apply StatMech.Lattice.mem_cornerFaces_of_corner a b c hc

/--
[support_faceBoundaryGraph_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma support_faceBoundaryGraph_subset_eq
  {S : Set (Site 2)} :
-- imply
  (faceBoundaryGraph S).support ⊆ ⋃ c ∈ S, (cornerFaces c : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.support_faceBoundaryGraph_subset S

/--
[exists_finset_support_faceBoundaryGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma exists_finset_support_faceBoundaryGraph_eq
  {S : Set (Site 2)}
-- given
  (hS : S.Finite) :
-- imply
  ∃ T : Finset (Site 2), (faceBoundaryGraph S).support ⊆ (T : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.exists_finset_support_faceBoundaryGraph S hS

/--
[exists_faceBoundaryGraph_adj_of_edgeBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma exists_faceBoundaryGraph_adj_of_edgeBoundary_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (h : (x, y) ∈ edgeBoundary 2 S) :
-- imply
  ∃ f g : Site 2, (faceBoundaryGraph S).Adj f g := by
-- proof
  apply StatMech.Lattice.exists_faceBoundaryGraph_adj_of_edgeBoundary S h

/--
[exists_dualCircuit_of_finite_of_edgeBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma exists_dualCircuit_of_finite_of_edgeBoundary_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hS : S.Finite)
  (hxy : (x, y) ∈ edgeBoundary 2 S) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph S).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Lattice.exists_dualCircuit_of_finite_of_edgeBoundary S hS hxy

/--
[exists_dualCircuit_of_finite_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean)
-/
@[path]
private lemma exists_dualCircuit_of_finite_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {z : Site 2}
  {w : (hypercubicLattice 2).Walk o z}
-- given
  (hfin : (cluster 2 ω o).Finite)
  (hz : z ∉ cluster 2 ω o) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Lattice.exists_dualCircuit_of_finite_cluster o hfin w hz


-- created on 2026-10-23
