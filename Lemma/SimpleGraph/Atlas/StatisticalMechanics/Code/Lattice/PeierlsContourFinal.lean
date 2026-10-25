import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[mem_componentSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma mem_componentSupport_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f g : Site 2} :
-- imply
  g ∈ componentSupport K T f ↔ g ∈ T ∧ (faceBoundaryGraph K).Reachable f g := by
-- proof
  apply StatMech.Lattice.mem_componentSupport

/--
[self_mem_componentSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma self_mem_componentSupport_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f : Site 2}
-- given
  (hf : f ∈ T) :
-- imply
  f ∈ componentSupport K T f := by
-- proof
  apply StatMech.Lattice.self_mem_componentSupport hf

/--
[componentSupport_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentSupport_neighbor_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f g h : Site 2}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
  (hg : g ∈ componentSupport K T f)
  (hadj : (faceBoundaryGraph K).Adj g h) :
-- imply
  h ∈ componentSupport K T f := by
-- proof
  apply StatMech.Lattice.componentSupport_neighbor hsupp hg hadj

/--
[componentSupport_walk_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentSupport_walk_subset_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f g : Site 2}
  {p : (faceBoundaryGraph K).Walk f g}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
  (hf : f ∈ T) :
-- imply
  ∀ v ∈ p.support, v ∈ componentSupport K T f := by
-- proof
  apply StatMech.Lattice.componentSupport_walk_subset hsupp hf p

/--
[componentGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_adj_eq
  {K : Set (Site 2)}
  {f a b : Site 2} :
-- imply
  (componentGraph K f).Adj a b ↔ (faceBoundaryGraph K).Adj a b ∧ (faceBoundaryGraph K).Reachable f a ∧ (faceBoundaryGraph K).Reachable f b := by
-- proof
  apply StatMech.Lattice.componentGraph_adj K f a b

/--
[componentGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_le_eq
  {K : Set (Site 2)}
  {f : Site 2} :
-- imply
  componentGraph K f ≤ faceBoundaryGraph K := by
-- proof
  apply StatMech.Lattice.componentGraph_le K f

/--
[componentGraph_neighborSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_neighborSet_eq_eq
  {K : Set (Site 2)}
  {f a : Site 2}
-- given
  (ha : (faceBoundaryGraph K).Reachable f a) :
-- imply
  (componentGraph K f).neighborSet a = (faceBoundaryGraph K).neighborSet a := by
-- proof
  apply StatMech.Lattice.componentGraph_neighborSet_eq ha

/--
[componentGraph_neighborSet_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_neighborSet_empty_eq
  {K : Set (Site 2)}
  {f a : Site 2}
-- given
  (ha : ¬ (faceBoundaryGraph K).Reachable f a) :
-- imply
  (componentGraph K f).neighborSet a = ∅ := by
-- proof
  apply StatMech.Lattice.componentGraph_neighborSet_empty ha

/--
[componentGraph_degree_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_degree_even_eq
  {K : Set (Site 2)}
  {f a : Site 2} :
-- imply
  Even ((componentGraph K f).degree a) := by
-- proof
  apply StatMech.Lattice.componentGraph_degree_even K f a

/--
[componentGraph_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_support_subset_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f : Site 2}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) :
-- imply
  (componentGraph K f).support ⊆ (componentSupport K T f : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.componentGraph_support_subset hsupp f

/--
[componentGraph_walk_in_componentSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_walk_in_componentSupport_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f : Site 2}
  {g : Site 2}
  {p : (componentGraph K f).Walk f g}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
  (hf : f ∈ T) :
-- imply
  ∀ v ∈ p.support, v ∈ componentSupport K T f := by
-- proof
  apply StatMech.Lattice.componentGraph_walk_in_componentSupport hsupp hf p

/--
[componentGraph_edge_of_walk_from_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_edge_of_walk_from_base_eq
  {K : Set (Site 2)}
  {f g : Site 2}
  {q : (faceBoundaryGraph K).Walk f g}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ q.edges) :
-- imply
  e ∈ (componentGraph K f).edgeSet := by
-- proof
  apply StatMech.Lattice.componentGraph_edge_of_walk_from_base q he

/--
[componentGraph_reachable_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_reachable_of_reachable_eq
  {K : Set (Site 2)}
  {f g : Site 2}
-- given
  (h : (faceBoundaryGraph K).Reachable f g) :
-- imply
  (componentGraph K f).Reachable f g := by
-- proof
  apply StatMech.Lattice.componentGraph_reachable_of_reachable h

/--
[reachable_induce_of_walk_in_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma reachable_induce_of_walk_in_set_eq
  {G : SimpleGraph V}
  {S : Set V}
  {a b : V}
  {p : G.Walk a b}
-- given
  (hsub : ∀ v ∈ p.support, v ∈ S)
  (ha : a ∈ S) :
-- imply
  (G.induce S).Reachable ⟨a, ha⟩ ⟨b, hsub b p.end_mem_support⟩ := by
-- proof
  apply StatMech.Lattice.reachable_induce_of_walk_in_set p hsub ha

/--
[componentGraph_support_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_support_walk_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f : Site 2}
  {a b : Site 2}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
  (hf : f ∈ T)
  (ha : a ∈ componentSupport K T f)
  (hb : b ∈ componentSupport K T f) :
-- imply
  ∃ p : (componentGraph K f).Walk a b, ∀ v ∈ p.support, v ∈ componentSupport K T f := by
-- proof
  apply StatMech.Lattice.componentGraph_support_walk hsupp hf ha hb

/--
[componentGraph_induce_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentGraph_induce_connected_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f : Site 2}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
  (hf : f ∈ T) :
-- imply
  ((componentGraph K f).induce (componentSupport K T f : Set (Site 2))).Connected := by
-- proof
  apply StatMech.Lattice.componentGraph_induce_connected hsupp hf

/--
[componentEulerCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentEulerCircuit_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f : Site 2}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
  (hf : f ∈ T) :
-- imply
  ∃ c : (componentGraph K f).Walk f f, c.IsTrail ∧ ∀ e ∈ (componentGraph K f).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Lattice.componentEulerCircuit hsupp hf

/--
[dualCircuit_of_componentCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma dualCircuit_of_componentCovers_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f : Site 2}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
  (hf : f ∈ T)
  (hcov : ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ (componentGraph K f).edgeSet) :
-- imply
  ∃ c : (faceBoundaryGraph K).Walk f f, c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Lattice.dualCircuit_of_componentCovers hsupp hf hcov

/--
[axisContourDualCircuit_of_tightData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma axisContourDualCircuit_of_tightData_eq
  {n ℓ : ℕ}
-- given
  (h : TightAxisCircuitData n ℓ) :
-- imply
  AxisContourDualCircuit 2 n ℓ := by
-- proof
  apply StatMech.Lattice.axisContourDualCircuit_of_tightData h

/--
[realisedContourWalkEncoding_of_tightData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma realisedContourWalkEncoding_of_tightData_eq
  {n ℓ : ℕ}
-- given
  (h : TightAxisCircuitData n ℓ) :
-- imply
  RealisedContourWalkEncoding 2 n ℓ := by
-- proof
  apply StatMech.Lattice.realisedContourWalkEncoding_of_tightData h

/--
[contourSubsetCountBound_of_tightData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma contourSubsetCountBound_of_tightData_eq
  {n ℓ : ℕ}
-- given
  (h : TightAxisCircuitData n ℓ) :
-- imply
  ContourSubsetCountBound 2 n ℓ := by
-- proof
  apply StatMech.Lattice.contourSubsetCountBound_of_tightData h

/--
[peierls_long_range_order_of_tightData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma peierls_long_range_order_of_tightData_eq
-- given
  (h : ∀ (n ℓ : ℕ), TightAxisCircuitData n ℓ) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → StatMech.Ising.plusMeasure 2 n β 0 ≠ StatMech.Ising.minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Lattice.peierls_long_range_order_of_tightData h

/--
[componentCovers_of_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma componentCovers_of_faceBoundaryConnected_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f : Site 2}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
  (hconn : FaceBoundaryConnected K T)
  (hf : f ∈ T) :
-- imply
  ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ (componentGraph K f).edgeSet := by
-- proof
  apply StatMech.Lattice.componentCovers_of_faceBoundaryConnected hsupp hconn hf

/--
[tightAxisCircuitData_instance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma tightAxisCircuitData_instance_eq
  {n ℓ : ℕ}
  {F : Finset (Sym2 (Site 2))}
  {K : Finset (Site 2)}
  {T : Finset (Site 2)}
  {j : ℕ}
-- given
  (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n)
  (hKcross : crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = F)
  (hKlen : contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ)
  (hsupp : (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)))
  (hconn : FaceBoundaryConnected (↑K : Set (Site 2)) T)
  (hj : j < ℓ)
  (hax : axisVertex 2 j ∈ T) :
-- imply
  ∃ K' : Finset (Site 2), (↑K' : Set (Site 2)) ⊆ box 2 n ∧ crossEdges (↑K' : Set (Site 2)) (bondFinsetTouch 2 n) = F ∧ contourLen (↑K' : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ ∧ ∃ (T' : Finset (Site 2)) (j' : ℕ), (faceBoundaryGraph (↑K' : Set (Site 2))).support ⊆ (T' : Set (Site 2)) ∧ j' < ℓ ∧ axisVertex 2 j' ∈ T' ∧ (∀ e ∈ (faceBoundaryGraph (↑K' : Set (Site 2))).edgeSet, e ∈ (componentGraph (↑K' : Set (Site 2)) (axisVertex 2 j')).edgeSet) := by
-- proof
  apply StatMech.Lattice.tightAxisCircuitData_instance hKbox hKcross hKlen hsupp hconn hj hax

/--
[axisVertex_two_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma axisVertex_two_zero_eq :
-- imply
  axisVertex 2 0 = (![0, 0] : Site 2) := by
-- proof
  apply StatMech.Lattice.axisVertex_two_zero

/--
[axisVertex_zero_mem_singletonBoundarySupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma axisVertex_zero_mem_singletonBoundarySupport_eq :
-- imply
  axisVertex 2 0 ∈ singletonBoundarySupport := by
-- proof
  apply StatMech.Lattice.axisVertex_zero_mem_singletonBoundarySupport

/--
[singletonOrigin_tight_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma singletonOrigin_tight_dualCircuit_eq :
-- imply
  ∃ c : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk (axisVertex 2 0) (axisVertex 2 0), c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Lattice.singletonOrigin_tight_dualCircuit

/--
[singletonOrigin_componentCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma singletonOrigin_componentCovers_eq :
-- imply
  ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet, e ∈ (componentGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (axisVertex 2 0)).edgeSet := by
-- proof
  apply StatMech.Lattice.singletonOrigin_componentCovers

/--
[axisVertex_two_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma axisVertex_two_natCast_eq
  {m : ℕ} :
-- imply
  axisVertex 2 m = (![(m : ℤ), 0] : Site 2) := by
-- proof
  apply StatMech.Lattice.axisVertex_two_natCast m

/--
[axisVertex_m_mem_boxFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma axisVertex_m_mem_boxFrame_eq
  {m n : ℕ} :
-- imply
  axisVertex 2 m ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.axisVertex_m_mem_boxFrame m n

/--
[boxCluster_componentCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma boxCluster_componentCovers_eq
  {m n : ℕ} :
-- imply
  ∀ e ∈ (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).edgeSet, e ∈ (componentGraph (↑(boxCluster m n) : Set (Site 2)) (axisVertex 2 m)).edgeSet := by
-- proof
  apply StatMech.Lattice.boxCluster_componentCovers m n

/--
[boxCluster_tight_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma boxCluster_tight_dualCircuit_eq
  {m n : ℕ} :
-- imply
  ∃ c : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk (axisVertex 2 m) (axisVertex 2 m), c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Lattice.boxCluster_tight_dualCircuit m n

/--
[tightAxisCircuitData_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma tightAxisCircuitData_of_empty_eq
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours 2 n ℓ = ∅) :
-- imply
  TightAxisCircuitData n ℓ := by
-- proof
  apply StatMech.Lattice.tightAxisCircuitData_of_empty hempty

/--
[contourSubsetCountBound_of_empty_tightData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean)
-/
@[path]
private lemma contourSubsetCountBound_of_empty_tightData_eq
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours 2 n ℓ = ∅) :
-- imply
  ContourSubsetCountBound 2 n ℓ := by
-- proof
  apply StatMech.Lattice.contourSubsetCountBound_of_empty_tightData hempty


-- created on 2026-10-23
