import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_centralFaceReachSet_openWalk_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFaceReachSet_openWalk_lift_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v : RlcConnectorVertex n}
  {w : (openSubgraphInduce 2 (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho) (rect (-2 * n) (2 * n) (-n) n)).Walk u v}
-- given
  (hu : (u : Site 2) ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho) :
-- imply
  ∃ hv : (v : Site 2) ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho, ((hypercubicLattice 2).induce (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_centralFaceReachSet_openWalk_lift gamma gamma' rho hu w

/--
[rlc_connectorCentralFaceReachSet_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceReachSet_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho)
  (hv : v ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho) :
-- imply
  ((hypercubicLattice 2).induce (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceReachSet_reachable gamma gamma' rho hu hv

/--
[rlc_connectorCentralFaceReachSet_reachable_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceReachSet_reachable_in_barrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho)
  (hv : v ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho) :
-- imply
  (latticeMinusBarrier (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Reachable u v := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceReachSet_reachable_in_barrier gamma gamma' rho hu hv

/--
[rlc_connectorCentralFaceExteriorComponent_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceExteriorComponent_infinite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  (rlc_connectorCentralFaceExteriorComponent gamma gamma' rho).supp.Infinite := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceExteriorComponent_infinite gamma gamma' rho

/--
[rlc_connectorCentralFaceReachSet_subset_filled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceReachSet_subset_filled_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorCentralFaceReachSet gamma gamma' rho ⊆ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho

/--
[rlc_connectorCentralFaceExteriorSet_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceExteriorSet_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho)
  (hv : v ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho) :
-- imply
  ((hypercubicLattice 2).induce (rlc_connectorCentralFaceExteriorSet gamma gamma' rho)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceExteriorSet_reachable gamma gamma' rho hu hv

/--
[rlc_connectorCentralFaceFilledReachSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledReachSet_finite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho).Finite := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho

/--
[rlc_connectorCentralFaceFilledReachSet_subset_connectorRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledReachSet_subset_connectorRect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hn : 0 < n) :
-- imply
  rlc_connectorCentralFaceFilledReachSet gamma gamma' rho ⊆ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledReachSet_subset_connectorRect hn gamma gamma' rho

/--
[rlc_connectorCentralFaceExteriorSet_reachable_in_filledBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceExteriorSet_reachable_in_filledBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho)
  (hv : v ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho) :
-- imply
  (latticeMinusBarrier (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable u v := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceExteriorSet_reachable_in_filledBarrier gamma gamma' rho hu hv

/--
[rlc_connectorCentralFaceFilledReachSet_reaches_reachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledReachSet_reaches_reachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u : Site 2}
-- given
  (hu : u ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
-- imply
  ∃ z : Site 2, ∃ hz : z ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho, ((hypercubicLattice 2).induce (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable ⟨u, hu⟩ ⟨z, rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho hz⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledReachSet_reaches_reachSet gamma gamma' rho hu

/--
[rlc_connectorCentralFaceFilledReachSet_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledReachSet_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
  (hv : v ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
-- imply
  ((hypercubicLattice 2).induce (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledReachSet_reachable gamma gamma' rho hu hv

/--
[rlc_connectorCentralFaceFilledReachSet_reachable_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledReachSet_reachable_in_barrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v : Site 2}
-- given
  (hu : u ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
  (hv : v ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
-- imply
  (latticeMinusBarrier (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable u v := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledReachSet_reachable_in_barrier gamma gamma' rho hu hv

/--
[rlc_connectorCentralFaceFilledReachSet_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledReachSet_faceBoundaryConnected_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  FaceBoundaryConnected (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) (phb_boundarySupport (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) (rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho)) := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledReachSet_faceBoundaryConnected gamma gamma' rho

/--
[rlc_connectorCentralFaceFilledBoundary_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledBoundary_degree_eq_two_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f : Site 2}
-- given
  (hf : f ∈ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support) :
-- imply
  (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).degree f = 2 := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledBoundary_degree_eq_two gamma gamma' rho hf

/--
[rlc_connectorCentralFaceFilledBoundary_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledBoundary_isCycles_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).IsCycles := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledBoundary_isCycles gamma gamma' rho

/--
[rlc_isCycle_of_isCycles_isTrail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_isCycle_of_isCycles_isTrail_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {v : V}
  {c : G.Walk v v}
-- given
  (hcycles : G.IsCycles)
  (hcne : c ≠ .nil)
  (hcTrail : c.IsTrail) :
-- imply
  c.IsCycle := by
-- proof
  apply StatMech.Universality.rlc_isCycle_of_isCycles_isTrail c hcycles hcne hcTrail

/--
[rlc_connectorCentralFaceFilledBoundary_other_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledBoundary_other_neighbor_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v) :
-- imply
  ∃ b : Site 2, (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b ∧ u ≠ b := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledBoundary_other_neighbor gamma gamma' rho huv

/--
[rlc_connectorCentralFaceFilledBoundary_existsUnique_other_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledBoundary_existsUnique_other_neighbor_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v) :
-- imply
  ∃! b : Site 2, u ≠ b ∧ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledBoundary_existsUnique_other_neighbor gamma gamma' rho huv

/--
[rlc_connectorCentralFaceFilledBoundary_inside_mem_reachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledBoundary_inside_mem_reachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Site 2}
-- given
  (hp : p ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
  (hq : q ∉ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  p ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledBoundary_inside_mem_reachSet gamma gamma' rho hp hq hpq

/--
[rlc_connectorCentralFaceFilled_edgeBoundary_subset_reachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilled_edgeBoundary_subset_reachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Site 2}
-- given
  (hpq : (p, q) ∈ edgeBoundary 2 (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) :
-- imply
  (p, q) ∈ edgeBoundary 2 (rlc_connectorCentralFaceReachSet gamma gamma' rho) := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilled_edgeBoundary_subset_reachSet gamma gamma' rho hpq

/--
[rlc_connectorCentralFaceFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) ≤ faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho) := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph gamma gamma' rho

/--
[rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f g : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hfg : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
-- imply
  sharedPrimalEdge f g ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure gamma gamma' rho hno hfg

/--
[rlc_connectorCentralFaceFilledFaceBoundary_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceFilledFaceBoundary_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f g : Site 2}
-- given
  (hf : f ∈ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support)
  (hg : g ∈ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support) :
-- imply
  (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable f g := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceFilledFaceBoundary_reachable gamma gamma' rho hf hg

/--
[rlc_centralFaceReachSet_verticalGap_outer_boundary_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFaceReachSet_verticalGap_outer_boundary_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ t : Int, (gamma.1.1 : Site 2) 1 ≤ t ∧ t < (gamma'.1.2.1 : Site 2) 1 ∧ ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧ (∀ s : Int, t < s → s ≤ (gamma'.1.2.1 : Site 2) 1 → ![0, s] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho) ∧ ((![0, t], ![0, t + 1]) ∈ edgeBoundary 2 (rlc_connectorCentralFaceReachSet gamma gamma' rho)) := by
-- proof
  apply StatMech.Universality.rlc_centralFaceReachSet_verticalGap_outer_boundary_of_failure gamma gamma' hposition rho hno

/--
[rlc_centralFace_verticalGap_outside_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFace_verticalGap_outside_mem_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ t : Int, (gamma.1.1 : Site 2) 1 ≤ t ∧ t < (gamma'.1.2.1 : Site 2) 1 ∧ ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧ (∀ s : Int, t < s → s ≤ (gamma'.1.2.1 : Site 2) 1 → ![0, s] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho) ∧ ![0, t + 1] ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_centralFace_verticalGap_outside_mem_exterior gamma gamma' hposition rho hno

/--
[rlc_centralFaceFilled_verticalGap_boundary_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFaceFilled_verticalGap_boundary_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ t : Int, (gamma.1.1 : Site 2) 1 ≤ t ∧ t < (gamma'.1.2.1 : Site 2) 1 ∧ ![0, t] ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho ∧ ![0, t + 1] ∉ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho ∧ ((![0, t], ![0, t + 1]) ∈ edgeBoundary 2 (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) := by
-- proof
  apply StatMech.Universality.rlc_centralFaceFilled_verticalGap_boundary_of_failure gamma gamma' hposition rho hno

/--
[RlcCentralFaceRetainedAnchoredBoundary.contour_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma contour_isCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho} :
-- imply
  B.contour.IsCycle := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.contour_isCycle B

/--
[RlcCentralFaceRetainedAnchoredBoundary.exists_orientedAnchorCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma exists_orientedAnchorCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho} :
-- imply
  ∃ c : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk B.firstFace B.firstFace, c.IsCycle ∧ c.snd = B.secondFace ∧ c.toSubgraph.verts = B.contour.toSubgraph.verts := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.exists_orientedAnchorCycle B

/--
[RlcCentralFaceRetainedAnchoredBoundary.exactComplementaryAnchorPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma exactComplementaryAnchorPath_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho} :
-- imply
  ∃ a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk B.secondFace B.firstFace, a.IsPath ∧ s(B.firstFace, B.secondFace) ∉ a.edges ∧ ∀ e : Sym2 (Site 2), e ∈ B.contour.edges ↔ e = s(B.firstFace, B.secondFace) ∨ e ∈ a.edges := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.exactComplementaryAnchorPath B

/--
[rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {z : Site 2}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hzPath : z ∈ rlc_pathVertices gamma'.1) :
-- imply
  z ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure gamma gamma' hposition rho hno hzPath

/--
[rlc_centralFaceLowestFilledAxisGap_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFaceLowestFilledAxisGap_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  Nonempty (RlcCentralFaceLowestFilledAxisGap gamma gamma' rho) := by
-- proof
  apply StatMech.Universality.rlc_centralFaceLowestFilledAxisGap_of_failure gamma gamma' hposition rho hno

/--
[RlcCentralFaceLowestFilledAxisGap.axis_successor_inside_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma axis_successor_inside_of_lt_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestFilledAxisGap gamma gamma' rho}
  {s : Int}
-- given
  (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
  (hs : s < L.height) :
-- imply
  (![0, s + 1] : Site 2) ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestFilledAxisGap.axis_successor_inside_of_lt L hsLower hs

/--
[RlcCentralFaceLowestFilledAxisGap.no_lower_axis_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma no_lower_axis_boundary_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestFilledAxisGap gamma gamma' rho}
  {s : Int}
-- given
  (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
  (hs : s < L.height) :
-- imply
  ((![0, s], ![0, s + 1]) ∉ edgeBoundary 2 (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestFilledAxisGap.no_lower_axis_boundary L hsLower hs

/--
[rlc_centralFace_retainedAnchoredBoundary_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFace_retainedAnchoredBoundary_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  Nonempty (RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) := by
-- proof
  apply StatMech.Universality.rlc_centralFace_retainedAnchoredBoundary_of_failure gamma gamma' hposition rho hno

/--
[rlc_centralFace_lowestRetainedAnchoredBoundary_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFace_lowestRetainedAnchoredBoundary_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hposition : RlcBookPositionedTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  Nonempty (RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) := by
-- proof
  apply StatMech.Universality.rlc_centralFace_lowestRetainedAnchoredBoundary_of_failure gamma gamma' hposition rho hno

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_axis_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma no_lower_axis_boundary_eq_2
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {s : Int}
-- given
  (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
  (hs : s < L.boundary.height) :
-- imply
  ((![0, s], ![0, s + 1]) ∉ edgeBoundary 2 (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_axis_boundary L hsLower hs

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_contour_axis_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma no_lower_contour_axis_crossing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {f g : Site 2}
  {s : Int}
-- given
  (hfg : s(f, g) ∈ L.boundary.contour.edges)
  (hshared : sharedPrimalEdge f g = s((![0, s] : Site 2), ![0, s + 1]))
  (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
  (hs : s < L.boundary.height) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_contour_axis_crossing L hfg hshared hsLower hs

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_reflected_axis_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma no_lower_reflected_axis_crossing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {f g : Site 2}
  {s : Int}
-- given
  (hfg : s(f, g) ∈ L.boundary.contour.edges)
  (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, s + 1] : Site 2), ![0, s + 1]))
  (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
  (hs : s < L.boundary.height) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_reflected_axis_crossing L hfg hreflected hsLower hs

/--
[rlc_faceBoundaryWalk_reflected_axis_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_faceBoundaryWalk_reflected_axis_crossing_eq
  {H : Set (Site 2)}
  {a b : Site 2}
  {p : (faceBoundaryGraph H).Walk a b}
-- given
  (ha : (rlc_dualReflect a) 0 < 0)
  (hb : 0 ≤ (rlc_dualReflect b) 0) :
-- imply
  ∃ (f g : Site 2) (k : Int), s(f, g) ∈ p.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]) := by
-- proof
  apply StatMech.Universality.rlc_faceBoundaryWalk_reflected_axis_crossing p ha hb

/--
[rlc_faceBoundaryWalk_first_reflected_axis_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_faceBoundaryWalk_first_reflected_axis_crossing_eq
  {H : Set (Site 2)}
  {a b : Site 2}
  {p : (faceBoundaryGraph H).Walk a b}
-- given
  (ha : (rlc_dualReflect a) 0 < 0)
  (hb : 0 ≤ (rlc_dualReflect b) 0) :
-- imply
  ∃ (u v : Site 2) (k : Int) (q : (faceBoundaryGraph H).Walk a u), (faceBoundaryGraph H).Adj u v ∧ s(u, v) ∈ p.edges ∧ (∀ e ∈ q.edges, e ∈ p.edges) ∧ (∀ z ∈ q.support, (rlc_dualReflect z) 0 < 0) ∧ s(rlc_dualReflect u, rlc_dualReflect v) = s((![-1, k] : Site 2), ![0, k]) := by
-- proof
  apply StatMech.Universality.rlc_faceBoundaryWalk_first_reflected_axis_crossing p ha hb

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_band_axis_crossing_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma no_lower_band_axis_crossing_walk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a b : Site 2}
  {p : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk a b}
-- given
  (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
  (ha : (rlc_dualReflect a) 0 < 0)
  (hb : 0 ≤ (rlc_dualReflect b) 0)
  (hpBand : ∀ z ∈ p.support, (gamma.1.1 : Site 2) 1 < (rlc_dualReflect z) 1 ∧ (rlc_dualReflect z) 1 ≤ L.boundary.height) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_band_axis_crossing_walk L p hpEdges ha hb hpBand

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.lower_band_walk_same_halfplane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma lower_band_walk_same_halfplane_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a b : Site 2}
  {p : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk a b}
-- given
  (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
  (hpBand : ∀ z ∈ p.support, (gamma.1.1 : Site 2) 1 < (rlc_dualReflect z) 1 ∧ (rlc_dualReflect z) 1 ≤ L.boundary.height) :
-- imply
  ((rlc_dualReflect a) 0 < 0 ↔ (rlc_dualReflect b) 0 < 0) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.lower_band_walk_same_halfplane L p hpEdges hpBand

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_band_strict_contact_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma no_lower_band_strict_contact_arc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {x y : Site 2}
  {p : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk y x}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxNe : rlc_dualReflect x ≠ (gamma.1.1 : Site 2))
  (hyNe : rlc_dualReflect y ≠ (gamma'.1.2.1 : Site 2))
  (hpBand : ∀ z ∈ p.support, (gamma.1.1 : Site 2) 1 < (rlc_dualReflect z) 1 ∧ (rlc_dualReflect z) 1 ≤ L.boundary.height) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_band_strict_contact_arc L hfaith p hpEdges hxPath hyPath hxNe hyNe hpBand

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma complementary_axis_arc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho} :
-- imply
  ∃ a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace, s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧ ∀ e ∈ a.edges, e ∈ L.boundary.contour.edges := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_arc L

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_path_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma complementary_axis_path_exact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho} :
-- imply
  ∃ a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace, a.IsPath ∧ s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧ ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_path_exact L

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.middlePath_axis_crossing_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma middlePath_axis_crossing_extreme_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
  {p : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk u v}
-- given
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hvPos : 0 < (rlc_dualReflect v) 0)
  (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
  (hpAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ p.edges) :
-- imply
  ∃ (f g : Site 2) (k : Int), s(f, g) ∈ p.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]) ∧ (k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.middlePath_axis_crossing_extreme L p huNeg hvPos hpEdges hpAvoid

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.middlePath_exits_lower_anchor_band](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma middlePath_exits_lower_anchor_band_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
  {p : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk u v}
-- given
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hvPos : 0 < (rlc_dualReflect v) 0)
  (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
  (hpAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ p.edges) :
-- imply
  ∃ z ∈ p.support, (rlc_dualReflect z) 1 ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height < (rlc_dualReflect z) 1 := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.middlePath_exits_lower_anchor_band L p huNeg hvPos hpEdges hpAvoid

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_crossing_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma complementary_axis_crossing_extreme_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho} :
-- imply
  ∃ (a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace) (f g : Site 2) (k : Int), s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧ (∀ e ∈ a.edges, e ∈ L.boundary.contour.edges) ∧ s(f, g) ∈ a.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]) ∧ (k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_crossing_extreme L

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma complementary_first_axis_crossing_extreme_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho} :
-- imply
  ∃ (a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace) (N u v : Site 2) (k : Int) (q : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk N u), (N = L.boundary.firstFace ∨ N = L.boundary.secondFace) ∧ rlc_dualReflect N = (![-1, L.boundary.height + 1] : Site 2) ∧ s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧ a.IsPath ∧ (∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges) ∧ (∀ e ∈ a.edges, e ∈ L.boundary.contour.edges) ∧ (∀ e ∈ q.edges, e ∈ a.edges) ∧ (∀ z ∈ q.support, (rlc_dualReflect z) 0 < 0) ∧ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧ s(u, v) ∈ a.edges ∧ s(rlc_dualReflect u, rlc_dualReflect v) = s((![-1, k] : Site 2), ![0, k]) ∧ (k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_extreme L

/--
[RlcCentralFaceRetainedAnchoredBoundary.filledReachSet_eq_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma filledReachSet_eq_leftRegion_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho} :
-- imply
  rlc_connectorCentralFaceFilledReachSet gamma gamma' rho = jec_leftRegion (B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.filledReachSet_eq_leftRegion B

/--
[RlcCentralFaceRetainedAnchoredBoundary.reflectedFilledReachSet_eq_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma reflectedFilledReachSet_eq_leftRegion_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho} :
-- imply
  rlc_reflectedPrimalRegion (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) = jec_leftRegion ((B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.reflectedFilledReachSet_eq_leftRegion B

/--
[rlc_bdEdge_reflectedPrimalRegion_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_bdEdge_reflectedPrimalRegion_map_eq
  {K : Set (Site 2)}
  {e : Sym2 (Site 2)} :
-- imply
  bdEdge (rlc_reflectedPrimalRegion K) (Sym2.map rlc_primalDualReflect e) ↔ bdEdge K e := by
-- proof
  apply StatMech.Universality.rlc_bdEdge_reflectedPrimalRegion_map K e

/--
[rlc_faceInterior_sharedPrimalEdge_endpoints_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_faceInterior_sharedPrimalEdge_endpoints_mem_rect_eq
  {a b c d : Int}
  {f g : Site 2}
-- given
  (hf : f ∈ rect a (b - 1) c (d - 1))
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rect a b c d ∧ q ∈ rect a b c d := by
-- proof
  apply StatMech.Universality.rlc_faceInterior_sharedPrimalEdge_endpoints_mem_rect hf hfg

/--
[rlc_reflectedCarrierFaces_mem_crossedBoxInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedCarrierFaces_mem_crossedBoxInterior_eq
  {n : Int}
  {f g z : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hz : z ∈ sharedPrimalEdge f g)
  (hzBox : z ∈ rect (-2 * n) (2 * n) (-n) n) :
-- imply
  rlc_dualReflect f ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1) ∧ rlc_dualReflect g ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_reflectedCarrierFaces_mem_crossedBoxInterior hfg hz hzBox

/--
[rlc_sharedPrimalEdge_mem_crossedBoxImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_sharedPrimalEdge_mem_crossedBoxImage_eq
  {n : Int}
  {f g p q : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hp : p ∈ rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2))
  (hq : q ∈ rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2)) :
-- imply
  sharedPrimalEdge f g ∈ (imageGraph (rlc_connectorCrossedBoxPlanar n)).edgeSet := by
-- proof
  apply StatMech.Universality.rlc_sharedPrimalEdge_mem_crossedBoxImage hfg hshared hp hq

/--
[rlc_crossedBox_interiorFace_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_crossedBox_interiorFace_isolated_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hf : f ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1)) :
-- imply
  ¬ (whb_faceRegion (imageGraph (rlc_connectorCrossedBoxPlanar n))).Adj f g := by
-- proof
  apply StatMech.Universality.rlc_crossedBox_interiorFace_isolated hf

/--
[rlc_crossedBox_interiorFace_component_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_crossedBox_interiorFace_component_singleton_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hf : f ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1))
  (hcomp : (whb_faceRegion (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk f = (whb_faceRegion (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk g) :
-- imply
  f = g := by
-- proof
  apply StatMech.Universality.rlc_crossedBox_interiorFace_component_singleton hf hcomp

/--
[rlc_connectorReflectedFilledCut_isEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorReflectedFilledCut_isEven_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  Ising.kwg_IsEven (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) (rlc_connectorReflectedFilledCut gamma gamma' rho) := by
-- proof
  apply StatMech.Universality.rlc_connectorReflectedFilledCut_isEven gamma gamma' rho

/--
[rlc_mem_reflectedFilledCut_iff_bdEdge_embedded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_mem_reflectedFilledCut_iff_bdEdge_embedded_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)} :
-- imply
  e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho ↔ bdEdge (rlc_reflectedPrimalRegion (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) (Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e) := by
-- proof
  apply StatMech.Universality.rlc_mem_reflectedFilledCut_iff_bdEdge_embedded gamma gamma' rho e

/--
[rlc_reflectedFilledBoundary_endpoints_mem_crossedBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedFilledBoundary_endpoints_mem_crossedBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Site 2}
-- given
  (hn : 0 < n)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hbd : bdEdge (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p, q)) :
-- imply
  rlc_primalDualReflect p ∈ rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2) ∧ rlc_primalDualReflect q ∈ rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2) := by
-- proof
  apply StatMech.Universality.rlc_reflectedFilledBoundary_endpoints_mem_crossedBox hn gamma gamma' rho hpq hbd

/--
[rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f g : Site 2}
-- given
  (hn : 0 < n)
  (hfg : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
-- imply
  rlc_dualReflect f ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1) ∧ rlc_dualReflect g ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior hn gamma gamma' rho hfg

/--
[rlc_sharedPrimalEdge_dualReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_sharedPrimalEdge_dualReflect_eq
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) = sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) := by
-- proof
  apply StatMech.Universality.rlc_sharedPrimalEdge_dualReflect hfg

/--
[rlc_reflectedFilledCutEdge_exists_faceBoundaryCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedFilledCutEdge_exists_faceBoundaryCarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
-- given
  (heCut : e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho) :
-- imply
  ∃ f g : Site 2, (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g ∧ Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e = sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) := by
-- proof
  apply StatMech.Universality.rlc_reflectedFilledCutEdge_exists_faceBoundaryCarrier gamma gamma' rho e heCut

/--
[rlc_faceBoundaryEdge_exists_reflectedFilledCutEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_faceBoundaryEdge_exists_reflectedFilledCutEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f g : Site 2}
-- given
  (hn : 0 < n)
  (hfg : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
-- imply
  ∃ e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n), Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e = sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) ∧ e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_faceBoundaryEdge_exists_reflectedFilledCutEdge hn gamma gamma' rho hfg

/--
[rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents_eq
  {n : Int}
  {f g : Site 2}
  {e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (he : Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e = sharedPrimalEdge f g) :
-- imply
  Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e = s((whb_faceRegion (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk f, (whb_faceRegion (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk g) := by
-- proof
  apply StatMech.Universality.rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents hfg e he

/--
[rlc_reflectedFilledCut_incident_component_out_mem_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedFilledCut_incident_component_out_mem_interior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
  {C : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
-- given
  (hn : 0 < n)
  (heCut : e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho)
  (hinc : Ising.kwg_incidentMod2 C (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e)) :
-- imply
  C.out ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_reflectedFilledCut_incident_component_out_mem_interior hn gamma gamma' rho heCut hinc

/--
[rlc_reflectedFilledCut_incident_component_ne_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedFilledCut_incident_component_ne_outer_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
  {C : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
-- given
  (hn : 0 < n)
  (heCut : e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho)
  (hinc : Ising.kwg_incidentMod2 C (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e)) :
-- imply
  C ≠ rlc_crossedBoxOuterFace n := by
-- proof
  apply StatMech.Universality.rlc_reflectedFilledCut_incident_component_ne_outer hn gamma gamma' rho heCut hinc

/--
[rlc_minimalReflectedCutPiece_carrierReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_minimalReflectedCutPiece_carrierReachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {S : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))}
  {C D : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hSsub : S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho)
  (hSmin : RlcCentralFaceMinimalReflectedCutPiece S)
  (hCinc : ∃ e ∈ S, Ising.kwg_incidentMod2 C (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e))
  (hDinc : ∃ e ∈ S, Ising.kwg_incidentMod2 D (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e)) :
-- imply
  (rlc_reflectedFilledBoundaryGraph gamma gamma' rho).Reachable C.out D.out := by
-- proof
  apply StatMech.Universality.rlc_minimalReflectedCutPiece_carrierReachable hn gamma gamma' rho S hSsub hSmin hCinc hDinc

/--
[rlc_minimalReflectedCutPiece_boundaryCarriers_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_minimalReflectedCutPiece_boundaryCarriers_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {S : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))}
  {f g p q : Site 2}
  {e e' : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hSsub : S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho)
  (hSmin : RlcCentralFaceMinimalReflectedCutPiece S)
  (hfg : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g)
  (hpq : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj p q)
  (heS : e ∈ S)
  (he'S : e' ∈ S)
  (he : Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e = sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g))
  (he' : Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e' = sharedPrimalEdge (rlc_dualReflect p) (rlc_dualReflect q)) :
-- imply
  (rlc_reflectedFilledBoundaryGraph gamma gamma' rho).Reachable (rlc_dualReflect f) (rlc_dualReflect p) := by
-- proof
  apply StatMech.Universality.rlc_minimalReflectedCutPiece_boundaryCarriers_reachable hn gamma gamma' rho S hSsub hSmin hfg hpq heS he'S he he'

/--
[rlc_faceBoundaryEdge_exists_minimalReflectedCutPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_faceBoundaryEdge_exists_minimalReflectedCutPeel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {f g : Site 2}
-- given
  (hn : 0 < n)
  (hfg : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
-- imply
  ∃ (e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)) (S R : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))), Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e = sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) ∧ S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho ∧ e ∈ S ∧ RlcCentralFaceMinimalReflectedCutPiece S ∧ R = rlc_connectorReflectedFilledCut gamma gamma' rho \ S ∧ Ising.kwg_IsEven (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) R ∧ Disjoint S R ∧ S ∪ R = rlc_connectorReflectedFilledCut gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_faceBoundaryEdge_exists_minimalReflectedCutPeel hn gamma gamma' rho hfg

/--
[rlc_sharedPrimalEdge_eq_unshift_flankFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_sharedPrimalEdge_eq_unshift_flankFaces_eq
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  sharedPrimalEdge x y = Sym2.map phb_doubleDualEquiv.symm (flankFaces x y) := by
-- proof
  apply StatMech.Universality.rlc_sharedPrimalEdge_eq_unshift_flankFaces hxy

/--
[rlc_map_flankFaces_primalDualReflect_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_map_flankFaces_primalDualReflect_symm_eq
  {p q : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  Sym2.map rlc_dualReflect (flankFaces (rlc_primalDualReflect.symm p) (rlc_primalDualReflect.symm q)) = flankFaces p q := by
-- proof
  apply StatMech.Universality.rlc_map_flankFaces_primalDualReflect_symm hpq

/--
[rlc_sharedPrimalEdge_endpoint_mem_connectorBox_of_faceBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_sharedPrimalEdge_endpoint_mem_connectorBox_of_faceBox_eq
  {n : Int}
  {f g x : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hfBox : f ∈ rlc_connectorFaceBox n)
  (_hgBox : g ∈ rlc_connectorFaceBox n)
  (hx : x ∈ sharedPrimalEdge f g) :
-- imply
  x ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_sharedPrimalEdge_endpoint_mem_connectorBox_of_faceBox hfg hfBox _hgBox hx

/--
[RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_covers_leftRegionBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma reflectedContour_covers_leftRegionBoundary_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {p q : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q)
  (hbd : bdEdge (jec_leftRegion ((B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom)) s(p, q)) :
-- imply
  flankFaces p q ∈ ((B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom).edges := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_covers_leftRegionBoundary B hpq hbd

/--
[RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_edge_sideToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma reflectedContour_edge_sideToggle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {f g : Site 2}
-- given
  (hfg : s(f, g) ∈ B.contour.edges) :
-- imply
  let C := (B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ (((rlc_primalDualReflect p ∈ jec_leftRegion C) ∧ rlc_primalDualReflect q ∉ jec_leftRegion C) ∨ (rlc_primalDualReflect p ∉ jec_leftRegion C ∧ rlc_primalDualReflect q ∈ jec_leftRegion C)) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_edge_sideToggle B hfg

/--
[RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_edge_shiftedFlank_sideToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma reflectedContour_edge_shiftedFlank_sideToggle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {f g : Site 2}
-- given
  (hfg : s(f, g) ∈ B.contour.edges) :
-- imply
  let C := (B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom ∃ h k : Site 2, flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(h, k) ∧ (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧ phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨ (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧ phb_doubleDualEquiv.symm k ∈ jec_leftRegion C)) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_edge_shiftedFlank_sideToggle B hfg

/--
[RlcCentralFaceRetainedAnchoredBoundary.reflectedBoundaryEdge_namedFlank_sideToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma reflectedBoundaryEdge_namedFlank_sideToggle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {f g h : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g)
  (hh : h ∈ flankFaces (rlc_dualReflect f) (rlc_dualReflect g)) :
-- imply
  let C := (B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom ∃ k : Site 2, flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(h, k) ∧ (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧ phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨ (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧ phb_doubleDualEquiv.symm k ∈ jec_leftRegion C)) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.reflectedBoundaryEdge_namedFlank_sideToggle B hfg hh

/--
[rlc_connectorCentralFaceRegion_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceRegion_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {h k : Site 2}
-- given
  (hh : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hk : k ∈ rlc_connectorCentralFaceRegion gamma gamma') :
-- imply
  ∃ (hhBox : h ∈ rlc_connectorFaceBox n) (hkBox : k ∈ rlc_connectorFaceBox n), (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable ⟨h, hhBox⟩ ⟨k, hkBox⟩ := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceRegion_reachable hh hk

/--
[RlcCentralFaceRetainedAnchoredBoundary.pairedCentralIncomingFlanks_cutReachable_and_sideToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma pairedCentralIncomingFlanks_cutReachable_and_sideToggle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {t u h t' u' h' : Site 2}
-- given
  (htu : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj t u)
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hhFlank : h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u))
  (ht'u' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj t' u')
  (hh'Region : h' ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh'Flank : h' ∈ flankFaces (rlc_dualReflect t') (rlc_dualReflect u')) :
-- imply
  ∃ (hhBox : h ∈ rlc_connectorFaceBox n) (hh'Box : h' ∈ rlc_connectorFaceBox n), (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable ⟨h, hhBox⟩ ⟨h', hh'Box⟩ ∧ ∃ k k' : Site 2, flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧ flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧ (let C := (B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧ phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨ (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧ phb_doubleDualEquiv.symm k ∈ jec_leftRegion C))) ∧ (let C := (B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom (((phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧ phb_doubleDualEquiv.symm k' ∉ jec_leftRegion C) ∨ (phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C ∧ phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C))) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.pairedCentralIncomingFlanks_cutReachable_and_sideToggle B htu hhRegion hhFlank ht'u' hh'Region hh'Flank

/--
[RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_hits_reflectedContour_of_oppositeSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma centralCutPath_hits_reflectedContour_of_oppositeSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {h h' : Site 2}
-- given
  (hhBox : h ∈ rlc_connectorFaceBox n)
  (hh'Box : h' ∈ rlc_connectorFaceBox n)
  (hreach : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable ⟨h, hhBox⟩ ⟨h', hh'Box⟩)
  (hopposite : let C := (B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom ((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ∧ phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C) ∨ (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧ phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C))) :
-- imply
  ∃ (z : RlcConnectorFaceVertex n) (f : Site 2), f ∈ B.contour.support ∧ phb_doubleDualEquiv.symm z.1 = rlc_dualReflect f := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_hits_reflectedContour_of_oppositeSide B hhBox hh'Box hreach hopposite

/--
[RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_goodContourEdge_of_oppositeSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma centralCutPath_goodContourEdge_of_oppositeSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {h h' : Site 2}
-- given
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hhBox : h ∈ rlc_connectorFaceBox n)
  (hh'Box : h' ∈ rlc_connectorFaceBox n)
  (hreach : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable ⟨h, hhBox⟩ ⟨h', hh'Box⟩)
  (hopposite : let C := (B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom ((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ∧ phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C) ∨ (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧ phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C))) :
-- imply
  ∃ (f g : Site 2) (z z' : RlcConnectorFaceVertex n), s(f, g) ∈ B.contour.edges ∧ (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj z z' ∧ z.1 ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ z'.1 ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(z.1, z'.1) ∧ rlc_dualReflect f ∈ rlc_connectorBox n ∧ rlc_dualReflect g ∈ rlc_connectorBox n ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_goodContourEdge_of_oppositeSide B hhRegion hhBox hh'Box hreach hopposite

/--
[rlc_flank_mem_vertexLoop_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_flank_mem_vertexLoop_support_eq
  {x z h : Site 2}
-- given
  (hxz : (hypercubicLattice 2).Adj x z)
  (hh : h ∈ flankFaces x z) :
-- imply
  h ∈ (jwc_vertexLoop (x 0) (x 1)).support := by
-- proof
  apply StatMech.Universality.rlc_flank_mem_vertexLoop_support hxz hh

/--
[rlc_vertexLoop_edges_mem_fourTraceFaceCutGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_vertexLoop_edges_mem_fourTraceFaceCutGraph_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x : Site 2}
-- given
  (hx : x ∉ rlc_connectorBarrier gamma gamma') :
-- imply
  ∀ e ∈ (jwc_vertexLoop (x 0) (x 1)).edges, e ∈ (rlc_connectorFourTraceFaceCutGraph gamma gamma').edgeSet := by
-- proof
  apply StatMech.Universality.rlc_vertexLoop_edges_mem_fourTraceFaceCutGraph gamma gamma' x hx

/--
[rlc_centralFaceRegion_flank_transfer_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFaceRegion_flank_transfer_interior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x z y h k : Site 2}
-- given
  (hxz : (hypercubicLattice 2).Adj x z)
  (hxy : (hypercubicLattice 2).Adj x y)
  (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧ -n < x 1 ∧ x 1 < n)
  (hxNot : x ∉ rlc_connectorBarrier gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces x z)
  (hk : k ∈ flankFaces x y) :
-- imply
  k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFaceRegion_flank_transfer_interior gamma gamma' hxz hxy hxInterior hxNot hhRegion hh hk

/--
[rlc_centralFaceRegion_other_flank_of_nonwall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFaceRegion_other_flank_of_nonwall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y h k : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y)
  (hnot : s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces x y)
  (hk : k ∈ flankFaces x y)
  (hkBox : k ∈ rlc_connectorFaceBox n) :
-- imply
  k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFaceRegion_other_flank_of_nonwall gamma gamma' hxy hnot hhRegion hh hk hkBox

/--
[rlc_incident_flank_intersection_of_not_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_incident_flank_intersection_of_not_opposite_eq
  {x a b : Site 2}
-- given
  (hxa : (hypercubicLattice 2).Adj x a)
  (hxb : (hypercubicLattice 2).Adj x b)
  (hab : a ≠ b)
  (hopp : ¬ (a 0 + b 0 = 2 * x 0 ∧ a 1 + b 1 = 2 * x 1)) :
-- imply
  ∃ k : Site 2, k ∈ flankFaces x a ∧ k ∈ flankFaces x b := by
-- proof
  apply StatMech.Universality.rlc_incident_flank_intersection_of_not_opposite hxa hxb hab hopp

/--
[rlc_flank_mem_connectorFaceBox_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_flank_mem_connectorFaceBox_of_interior_eq
  {n : Int}
  {x y h : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y)
  (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧ -n < x 1 ∧ x 1 < n)
  (hh : h ∈ flankFaces x y) :
-- imply
  h ∈ rlc_connectorFaceBox n := by
-- proof
  apply StatMech.Universality.rlc_flank_mem_connectorFaceBox_of_interior hxy hxInterior hh

/--
[rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x a b h : Site 2}
-- given
  (hxa : (hypercubicLattice 2).Adj x a)
  (hxb : (hypercubicLattice 2).Adj x b)
  (hab : a ≠ b)
  (hopp : ¬ (a 0 + b 0 = 2 * x 0 ∧ a 1 + b 1 = 2 * x 1))
  (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧ -n < x 1 ∧ x 1 < n)
  (hnot : s(x, a) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces x a) :
-- imply
  s(x, b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident gamma gamma' hxa hxb hab hopp hxInterior hnot hhRegion hh

/--
[rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x a b h : Site 2}
-- given
  (hxa : (hypercubicLattice 2).Adj x a)
  (hxb : (hypercubicLattice 2).Adj x b)
  (hab : a ≠ b)
  (hopp : ¬ (a 0 + b 0 = 2 * x 0 ∧ a 1 + b 1 = 2 * x 1))
  (hxBox : x ∈ rlc_connectorBox n)
  (hbBox : b ∈ rlc_connectorBox n)
  (hnot : s(x, a) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces x a)
  (hcommonBox : ∀ k : Site 2, k ∈ flankFaces x a → k ∈ flankFaces x b → k ∈ rlc_connectorFaceBox n) :
-- imply
  s(x, b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed gamma gamma' hxa hxb hab hopp hxBox hbBox hnot hhRegion hh hcommonBox

/--
[rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x a b h : Site 2}
-- given
  (hxa : (hypercubicLattice 2).Adj x a)
  (hxb : (hypercubicLattice 2).Adj x b)
  (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧ -n < x 1 ∧ x 1 < n)
  (hnotIn : s(x, a) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces x a)
  (hside : ∃ y : Site 2, (hypercubicLattice 2).Adj x y ∧ y ≠ a ∧ y ≠ b ∧ ¬ (a 0 + y 0 = 2 * x 0 ∧ a 1 + y 1 = 2 * x 1) ∧ ¬ (y 0 + b 0 = 2 * x 0 ∧ y 1 + b 1 = 2 * x 1) ∧ s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma') :
-- imply
  s(x, b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side gamma gamma' hxa hxb hxInterior hnotIn hhRegion hh hside

/--
[rlc_doubleDualShift_flipX_eq_dualReflect_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_doubleDualShift_flipX_eq_dualReflect_symm_eq
  {z : Site 2} :
-- imply
  phb_doubleDualShift (rlc_flipX z) = rlc_dualReflect.symm z := by
-- proof
  apply StatMech.Universality.rlc_doubleDualShift_flipX_eq_dualReflect_symm z

/--
[rlc_doubleDualShift_endpoint_mem_flankFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_doubleDualShift_endpoint_mem_flankFaces_eq
  {p q : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  phb_doubleDualShift p ∈ flankFaces p q ∨ phb_doubleDualShift q ∈ flankFaces p q := by
-- proof
  apply StatMech.Universality.rlc_doubleDualShift_endpoint_mem_flankFaces hpq

/--
[rlc_fourTrace_axis_vertex_height_eq_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_fourTrace_axis_vertex_height_eq_endpoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {k : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hk : (![0, k] : Site 2) ∈ rlc_connectorBarrier gamma gamma') :
-- imply
  k = (gamma.1.1 : Site 2) 1 ∨ k = (gamma'.1.2.1 : Site 2) 1 := by
-- proof
  apply StatMech.Universality.rlc_fourTrace_axis_vertex_height_eq_endpoint gamma gamma' hfaith k hk

/--
[rlc_axisCrossEdge_not_mem_fourTrace_of_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_axisCrossEdge_not_mem_fourTrace_of_between_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {k : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hlower : (gamma.1.1 : Site 2) 1 < k)
  (hupper : k < (gamma'.1.2.1 : Site 2) 1) :
-- imply
  s((![-1, k] : Site 2), ![0, k]) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisCrossEdge_not_mem_fourTrace_of_between gamma gamma' hfaith hlower hupper

/--
[rlc_axisGapFace_mem_connectorCentralFaceRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_axisGapFace_mem_connectorCentralFaceRegion_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (htLower : (gamma.1.1 : Site 2) 1 ≤ t)
  (htUpper : t < (gamma'.1.2.1 : Site 2) 1) :
-- imply
  (![-1, t] : Site 2) ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGapFace_mem_connectorCentralFaceRegion gamma gamma' hfaith htLower htUpper

/--
[rlc_axisGapHorizontal_mem_connectorCentralFacePlanarEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_axisGapHorizontal_mem_connectorCentralFacePlanarEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {k : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hkLower : (gamma.1.1 : Site 2) 1 < k)
  (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1) :
-- imply
  s((![-1, k] : Site 2), ![0, k]) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGapHorizontal_mem_connectorCentralFacePlanarEdges gamma gamma' hfaith hkLower hkUpper

/--
[RlcCentralFaceRetainedAnchoredBoundary.anchor_reflected_mem_planar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma anchor_reflected_mem_planar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.anchor_reflected_mem_planar B hfaith

/--
[rlc_faceBoundary_contact_of_flippedTrace_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_faceBoundary_contact_of_flippedTrace_exit_eq
  {a b c d : Int}
  {tau : RlcCrossingPath a b c d}
  {H : Set (Site 2)}
  {u : Site 2}
  {z : Site 2}
-- given
  (huPath : u ∈ rlc_pathVertices tau)
  (huIn : rlc_flipX u ∈ H)
  (hzPath : z ∈ rlc_pathVertices tau)
  (hzOut : rlc_flipX z ∉ H) :
-- imply
  ∃ x : Site 2, x ∈ (faceBoundaryGraph H).support ∧ rlc_dualReflect x ∈ rlc_pathVertices tau := by
-- proof
  apply StatMech.Universality.rlc_faceBoundary_contact_of_flippedTrace_exit tau H huPath huIn hzPath hzOut

/--
[rlc_bookFlippedTraceIntersection_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_bookFlippedTraceIntersection_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  RlcBookFlippedTraceIntersection gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_bookFlippedTraceIntersection_of_faithful gamma gamma' hfaith

/--
[rlc_bookFourTraceOrderedSides_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_bookFourTraceOrderedSides_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ (rightSide : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) (gamma'.1.2.1 : Site 2)) (leftSide : (hypercubicLattice 2).Walk (gamma'.1.2.1 : Site 2) (gamma.1.1 : Site 2)), (∀ e ∈ rightSide.edges, e ∈ rlc_pathEdges gamma.1 ∨ e ∈ rlc_reflectedPathEdges gamma'.1) ∧ (∀ z ∈ rightSide.support, 0 ≤ z 0) ∧ (∀ e ∈ leftSide.edges, e ∈ rlc_pathEdges gamma'.1 ∨ e ∈ rlc_reflectedPathEdges gamma.1) ∧ ∀ z ∈ leftSide.support, z 0 ≤ 0 := by
-- proof
  apply StatMech.Universality.rlc_bookFourTraceOrderedSides_of_faithful gamma gamma' hfaith

/--
[rlc_connectorBarrier_positive_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorBarrier_positive_classify_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz0 : 0 < z 0)
  (hz : z ∈ rlc_connectorBarrier gamma gamma') :
-- imply
  z ∈ rlc_pathVertices gamma.1 ∨ ∃ w ∈ rlc_pathVertices gamma'.1, z = rlc_flipX w := by
-- proof
  apply StatMech.Universality.rlc_connectorBarrier_positive_classify gamma gamma' hz0 hz

/--
[rlc_connectorBarrier_negative_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorBarrier_negative_classify_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz0 : z 0 < 0)
  (hz : z ∈ rlc_connectorBarrier gamma gamma') :
-- imply
  z ∈ rlc_pathVertices gamma'.1 ∨ ∃ w ∈ rlc_pathVertices gamma.1, z = rlc_flipX w := by
-- proof
  apply StatMech.Universality.rlc_connectorBarrier_negative_classify gamma gamma' hz0 hz

/--
[rlc_connectorBarrier_original_or_strict_reflected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorBarrier_original_or_strict_reflected_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_connectorBarrier gamma gamma') :
-- imply
  z ∈ rlc_pathVertices gamma.1 ∨ z ∈ rlc_pathVertices gamma'.1 ∨ (0 < z 0 ∧ ∃ w ∈ rlc_pathVertices gamma'.1, z = rlc_flipX w) ∨ (z 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1, z = rlc_flipX w) := by
-- proof
  apply StatMech.Universality.rlc_connectorBarrier_original_or_strict_reflected gamma gamma' hz

/--
[rlc_reflectedLeft_hit_sourceNE_not_filled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedLeft_hit_sourceNE_not_filled_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u w : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hw : w ∈ rlc_pathVertices gamma'.1)
  (hu : rlc_dualReflect u = rlc_flipX w) :
-- imply
  (![u 0 + 1, u 1 + 1] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_reflectedLeft_hit_sourceNE_not_filled gamma gamma' hfaith rho hno hw hu

/--
[rlc_reflectedRight_hit_sourceNE_mem_filled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedRight_hit_sourceNE_mem_filled_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u w : Site 2}
-- given
  (hw : w ∈ rlc_pathVertices gamma.1)
  (hu : rlc_dualReflect u = rlc_flipX w) :
-- imply
  (![u 0 + 1, u 1 + 1] : Site 2) ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_reflectedRight_hit_sourceNE_mem_filled gamma gamma' rho hw hu

/--
[rlc_faceBoundary_step_of_NE_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_faceBoundary_step_of_NE_not_mem_eq
  {H : Set (Site 2)}
  {u v : Site 2}
-- given
  (huv : (faceBoundaryGraph H).Adj u v)
  (hne : (![u 0 + 1, u 1 + 1] : Site 2) ∉ H) :
-- imply
  (v = ![u 0 + 1, u 1] ∧ (![u 0 + 1, u 1] : Site 2) ∈ H) ∨ v = ![u 0 - 1, u 1] ∨ (v = ![u 0, u 1 + 1] ∧ (![u 0, u 1 + 1] : Site 2) ∈ H) ∨ v = ![u 0, u 1 - 1] := by
-- proof
  apply StatMech.Universality.rlc_faceBoundary_step_of_NE_not_mem H huv hne

/--
[rlc_faceBoundary_step_of_NE_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_faceBoundary_step_of_NE_mem_eq
  {H : Set (Site 2)}
  {u v : Site 2}
-- given
  (huv : (faceBoundaryGraph H).Adj u v)
  (hne : (![u 0 + 1, u 1 + 1] : Site 2) ∈ H) :
-- imply
  (v = ![u 0 + 1, u 1] ∧ (![u 0 + 1, u 1] : Site 2) ∉ H) ∨ v = ![u 0 - 1, u 1] ∨ (v = ![u 0, u 1 + 1] ∧ (![u 0, u 1 + 1] : Site 2) ∉ H) ∨ v = ![u 0, u 1 - 1] := by
-- proof
  apply StatMech.Universality.rlc_faceBoundary_step_of_NE_mem H huv hne

/--
[rlc_reflectedHit_sharedPrimalEdge_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedHit_sharedPrimalEdge_right_eq
  {u w : Site 2}
-- given
  (hu : rlc_dualReflect u = rlc_flipX w) :
-- imply
  sharedPrimalEdge u ![u 0 + 1, u 1] = s((![w 0, w 1 - 1] : Site 2), w) := by
-- proof
  apply StatMech.Universality.rlc_reflectedHit_sharedPrimalEdge_right hu

/--
[rlc_reflectedHit_sharedPrimalEdge_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedHit_sharedPrimalEdge_top_eq
  {u w : Site 2}
-- given
  (hu : rlc_dualReflect u = rlc_flipX w) :
-- imply
  sharedPrimalEdge u ![u 0, u 1 + 1] = s((![w 0 - 1, w 1] : Site 2), w) := by
-- proof
  apply StatMech.Universality.rlc_reflectedHit_sharedPrimalEdge_top hu

/--
[rlc_reflectedHit_sharedPrimalEdge_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedHit_sharedPrimalEdge_left_eq
  {u w : Site 2}
-- given
  (hu : rlc_dualReflect u = rlc_flipX w) :
-- imply
  sharedPrimalEdge u ![u 0 - 1, u 1] = s((![w 0 - 1, w 1 - 1] : Site 2), ![w 0 - 1, w 1]) := by
-- proof
  apply StatMech.Universality.rlc_reflectedHit_sharedPrimalEdge_left hu

/--
[rlc_reflectedHit_sharedPrimalEdge_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedHit_sharedPrimalEdge_bottom_eq
  {u w : Site 2}
-- given
  (hu : rlc_dualReflect u = rlc_flipX w) :
-- imply
  sharedPrimalEdge u ![u 0, u 1 - 1] = s((![w 0 - 1, w 1 - 1] : Site 2), ![w 0, w 1 - 1]) := by
-- proof
  apply StatMech.Universality.rlc_reflectedHit_sharedPrimalEdge_bottom hu

/--
[rlc_reflectedHit_boundary_step_ne_right_of_south_exposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedHit_boundary_step_ne_right_of_south_exposed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v w : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hu : rlc_dualReflect u = rlc_flipX w)
  (hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  v ≠ ![u 0 + 1, u 1] := by
-- proof
  apply StatMech.Universality.rlc_reflectedHit_boundary_step_ne_right_of_south_exposed gamma gamma' rho hno huv hu hsouth

/--
[rlc_reflectedHit_boundary_step_ne_top_of_west_exposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedHit_boundary_step_ne_top_of_west_exposed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v w : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hu : rlc_dualReflect u = rlc_flipX w)
  (hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  v ≠ ![u 0, u 1 + 1] := by
-- proof
  apply StatMech.Universality.rlc_reflectedHit_boundary_step_ne_top_of_west_exposed gamma gamma' rho hno huv hu hwest

/--
[rlc_pathVertex_incident_edge_of_ne_finish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_pathVertex_incident_edge_of_ne_finish_eq
  {a b c d : Int}
  {tau : RlcCrossingPath a b c d}
  {w : Site 2}
-- given
  (hw : w ∈ rlc_pathVertices tau)
  (hne : w ≠ (tau.2.1 : Site 2)) :
-- imply
  ∃ r : Site 2, s(w, r) ∈ rlc_pathEdges tau := by
-- proof
  apply StatMech.Universality.rlc_pathVertex_incident_edge_of_ne_finish tau hw hne

/--
[rlc_reflectedPathEdge_endpoint_mem_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedPathEdge_endpoint_mem_vertices_eq
  {a b c d : Int}
  {tau : RlcCrossingPath a b c d}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_reflectedPathEdges tau)
  (hz : z ∈ e) :
-- imply
  ∃ w ∈ rlc_pathVertices tau, z = rlc_flipX w := by
-- proof
  apply StatMech.Universality.rlc_reflectedPathEdge_endpoint_mem_vertices tau he hz

/--
[rlc_mem_pathEdges_of_reflected_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_mem_pathEdges_of_reflected_mk_eq
  {a b c d : Int}
  {tau : RlcCrossingPath a b c d}
  {x y : Site 2}
-- given
  (he : s(rlc_flipX x, rlc_flipX y) ∈ rlc_reflectedPathEdges tau) :
-- imply
  s(x, y) ∈ rlc_pathEdges tau := by
-- proof
  apply StatMech.Universality.rlc_mem_pathEdges_of_reflected_mk tau he

/--
[rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hz : z ∈ e)
  (hzRight : z ∉ rlc_pathVertices gamma.1)
  (hzLeft : z ∉ rlc_pathVertices gamma'.1)
  (hzFlipRight : ¬ ∃ w ∈ rlc_pathVertices gamma.1, z = rlc_flipX w) :
-- imply
  e ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive gamma gamma' he hz hzRight hzLeft hzFlipRight

/--
[rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hz : z ∈ e)
  (hzRight : z ∉ rlc_pathVertices gamma.1)
  (hzLeft : z ∉ rlc_pathVertices gamma'.1)
  (hzFlipLeft : ¬ ∃ w ∈ rlc_pathVertices gamma'.1, z = rlc_flipX w) :
-- imply
  e ∈ rlc_reflectedPathEdges gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive gamma gamma' he hz hzRight hzLeft hzFlipLeft

/--
[rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {k : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  s((![0, k - 1] : Site 2), ![0, k]) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful gamma gamma' hfaith k

/--
[rlc_bookFourTraceAxisLoop_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_bookFourTraceAxisLoop_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ (c : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)), (gamma.1.1 : Site 2) ∈ c.support ∧ (gamma'.1.2.1 : Site 2) ∈ c.support ∧ (∀ e ∈ c.edges, e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧ (∀ k : Int, (gamma.1.1 : Site 2) 1 < k → k ≤ (gamma'.1.2.1 : Site 2) 1 → ¬ Even (jec_rayCount (![1, k] : Site 2) c)) := by
-- proof
  apply StatMech.Universality.rlc_bookFourTraceAxisLoop_of_faithful gamma gamma' hfaith

/--
[rlc_bookFourTraceAxisLoop_zeroRay_odd_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_bookFourTraceAxisLoop_zeroRay_odd_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ (c : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)), (∀ e ∈ c.edges, e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧ ∀ k : Int, (gamma.1.1 : Site 2) 1 < k → k ≤ (gamma'.1.2.1 : Site 2) 1 → ¬ Even (jec_rayCount (![0, k] : Site 2) c) := by
-- proof
  apply StatMech.Universality.rlc_bookFourTraceAxisLoop_zeroRay_odd_of_faithful gamma gamma' hfaith

/--
[rlc_bookFourTraceAxisLoop_zeroRay_parity_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_bookFourTraceAxisLoop_zeroRay_parity_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ (c : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)), (∀ e ∈ c.edges, e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧ (∀ k : Int, (gamma.1.1 : Site 2) 1 < k → k ≤ (gamma'.1.2.1 : Site 2) 1 → ¬ Even (jec_rayCount (![0, k] : Site 2) c)) ∧ ∀ k : Int, (k ≤ (gamma.1.1 : Site 2) 1 ∨ (gamma'.1.2.1 : Site 2) 1 < k) → Even (jec_rayCount (![0, k] : Site 2) c) := by
-- proof
  apply StatMech.Universality.rlc_bookFourTraceAxisLoop_zeroRay_parity_of_faithful gamma gamma' hfaith

/--
[rlc_axisInside_to_axisOutside_meets_connectorBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_axisInside_to_axisOutside_meets_connectorBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {kin kout : Int}
  {w : (hypercubicLattice 2).Walk (![0, kin] : Site 2) ![0, kout]}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hinLower : (gamma.1.1 : Site 2) 1 < kin)
  (hinUpper : kin ≤ (gamma'.1.2.1 : Site 2) 1)
  (hout : kout ≤ (gamma.1.1 : Site 2) 1 ∨ (gamma'.1.2.1 : Site 2) 1 < kout) :
-- imply
  ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisInside_to_axisOutside_meets_connectorBarrier gamma gamma' hfaith hinLower hinUpper hout w

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.boundaryPrefix_to_outsideAxis_meetsBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma boundaryPrefix_to_outsideAxis_meetsBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {N u v : Site 2}
  {k : Int}
  {p : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk N u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hN : rlc_dualReflect N = (![-1, L.boundary.height + 1] : Site 2))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) = s((![-1, k] : Site 2), ![0, k]))
  (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨ (gamma'.1.2.1 : Site 2) 1 < k) :
-- imply
  ∃ (w : (hypercubicLattice 2).Walk (![0, L.boundary.height + 1] : Site 2) ![0, k]), (∀ z ∈ w.support, z = (![0, L.boundary.height + 1] : Site 2) ∨ z = (![0, k] : Site 2) ∨ ∃ f ∈ p.support, z = rlc_dualReflect f) ∧ ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.boundaryPrefix_to_outsideAxis_meetsBarrier L hfaith p hN huNeg hreflected hkOutside

/--
[rlc_connectorBarrier_mem_connectorBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorBarrier_mem_connectorBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_connectorBarrier gamma gamma') :
-- imply
  z ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_connectorBarrier_mem_connectorBox gamma gamma' hz

/--
[rlc_connectorBoxBoundary_detour_avoidsBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorBoxBoundary_detour_avoidsBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {k : Int}
  {z : Site 2}
-- given
  (hzBoundary : z 0 = -2 * n ∨ z 0 = 2 * n ∨ z 1 = -n ∨ z 1 = n)
  (hzNot : z ∉ rlc_connectorBarrier gamma gamma') :
-- imply
  ∃ p : (hypercubicLattice 2).Walk z (![2 * n + 1, k] : Site 2), ∀ w ∈ p.support, w ∉ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorBoxBoundary_detour_avoidsBarrier gamma gamma' hzBoundary hzNot

/--
[rlc_axisGap_to_rightExterior_meets_connectorBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_axisGap_to_rightExterior_meets_connectorBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {k : Int}
  {w : (hypercubicLattice 2).Walk (![1, k] : Site 2) (![2 * n + 1, k] : Site 2)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hkLower : (gamma.1.1 : Site 2) 1 < k)
  (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1) :
-- imply
  ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGap_to_rightExterior_meets_connectorBarrier gamma gamma' hfaith hkLower hkUpper w

/--
[rlc_axisGapAxis_to_rightExterior_meets_connectorBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_axisGapAxis_to_rightExterior_meets_connectorBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {k : Int}
  {w : (hypercubicLattice 2).Walk (![0, k] : Site 2) (![2 * n + 1, k] : Site 2)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hkLower : (gamma.1.1 : Site 2) 1 < k)
  (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1) :
-- imply
  ∃ z ∈ w.support, z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_axisGapAxis_to_rightExterior_meets_connectorBarrier gamma gamma' hfaith hkLower hkUpper w

/--
[rlc_centralFaceFilledBoundaryContacts_of_flippedIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFaceFilledBoundaryContacts_of_flippedIntersection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hcross : RlcBookFlippedTraceIntersection gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryContacts gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_centralFaceFilledBoundaryContacts_of_flippedIntersection gamma gamma' hfaith hcross rho hno

/--
[rlc_centralFaceFilledBoundaryContacts_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFaceFilledBoundaryContacts_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryContacts gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_centralFaceFilledBoundaryContacts_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_centralFace_retainedAnchorContactWalk_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFace_retainedAnchorContactWalk_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) (x y : Site 2) (hx : x ∈ B.contour.support) (hy : y ∈ B.contour.support), rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ B.firstFace ∈ (rlc_centralFaceContactSubwalk B.contour hx hy).support ∧ ∀ e ∈ (rlc_centralFaceContactSubwalk B.contour hx hy).edges, e ∈ B.contour.edges := by
-- proof
  apply StatMech.Universality.rlc_centralFace_retainedAnchorContactWalk_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_centralFace_anchorToContacts_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFace_anchorToContacts_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) (x y : Site 2) (px : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk B.firstFace x) (py : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk B.firstFace y), rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ (∀ e ∈ px.edges, e ∈ B.contour.edges) ∧ ∀ e ∈ py.edges, e ∈ B.contour.edges := by
-- proof
  apply StatMech.Universality.rlc_centralFace_anchorToContacts_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_contourContactArcs_support_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_contourContactArcs_support_cover_eq
  {H : SimpleGraph (Site 2)}
  {u x y z : Site 2}
  {c : H.Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hz : z ∈ c.support) :
-- imply
  z ∈ (rlc_orderedContourArc c hx hy).support ∨ z ∈ (rlc_complementaryContourArc c hx hy).support := by
-- proof
  apply StatMech.Universality.rlc_contourContactArcs_support_cover c hx hy hz

/--
[rlc_contourContactArcs_edges_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_contourContactArcs_edges_decompose_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  (c.rotate x hx).edges = (rlc_orderedContourArc c hx hy).edges ++ (rlc_complementaryContourArc c hx hy).edges.reverse := by
-- proof
  apply StatMech.Universality.rlc_contourContactArcs_edges_decompose c hx hy

/--
[rlc_contourContactArcs_edges_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_contourContactArcs_edges_cover_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
  {e : Sym2 (Site 2)}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (he : e ∈ c.edges) :
-- imply
  e ∈ (rlc_orderedContourArc c hx hy).edges ∨ e ∈ (rlc_complementaryContourArc c hx hy).edges := by
-- proof
  apply StatMech.Universality.rlc_contourContactArcs_edges_cover c hx hy he

/--
[rlc_contourContactArcs_edges_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_contourContactArcs_edges_disjoint_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hc : c.IsTrail)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  List.Disjoint (rlc_orderedContourArc c hx hy).edges (rlc_complementaryContourArc c hx hy).edges := by
-- proof
  apply StatMech.Universality.rlc_contourContactArcs_edges_disjoint c hc hx hy

/--
[rlc_orderedContourArc_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_orderedContourArc_isPath_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  (rlc_orderedContourArc c hx hy).IsPath := by
-- proof
  apply StatMech.Universality.rlc_orderedContourArc_isPath c hc hx hy

/--
[rlc_complementaryContourArc_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_complementaryContourArc_isPath_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxy : x ≠ y) :
-- imply
  (rlc_complementaryContourArc c hx hy).IsPath := by
-- proof
  apply StatMech.Universality.rlc_complementaryContourArc_isPath c hc hx hy hxy

/--
[rlc_centralFace_anchoredContactChoice_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFace_anchoredContactChoice_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryAnchoredContactChoice gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_centralFace_anchoredContactChoice_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_reflectedEdgeCarrierGeometry_iff_planarEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedEdgeCarrierGeometry_iff_planarEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ↔ s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_reflectedEdgeCarrierGeometry_iff_planarEdges gamma gamma' hfg

/--
[RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_nonwallGoodContourEdge_of_oppositeSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma centralCutPath_nonwallGoodContourEdge_of_oppositeSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {h h' : Site 2}
-- given
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hhBox : h ∈ rlc_connectorFaceBox n)
  (hh'Box : h' ∈ rlc_connectorFaceBox n)
  (hreach : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable ⟨h, hhBox⟩ ⟨h', hh'Box⟩)
  (hopposite : let C := (B.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom ((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ∧ phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C) ∨ (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧ phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C))) :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ B.contour.edges ∧ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_nonwallGoodContourEdge_of_oppositeSide B hhRegion hhBox hh'Box hreach hopposite

/--
[rlc_reflected_axisCrossing_carrier_of_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflected_axisCrossing_carrier_of_between_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2}
  {k : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hfg : (hypercubicLattice 2).Adj f g)
  (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]))
  (hkLower : (gamma.1.1 : Site 2) 1 < k)
  (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_reflected_axisCrossing_carrier_of_between gamma gamma' hfaith hfg hreflected hkLower hkUpper

/--
[rlc_reflected_axisCrossing_carrier_of_right_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflected_axisCrossing_carrier_of_right_contact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2}
  {k : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hfNeg : (rlc_dualReflect f) 0 < 0)
  (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]))
  (hgPath : rlc_dualReflect g ∈ rlc_pathVertices gamma.1) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_reflected_axisCrossing_carrier_of_right_contact gamma gamma' hfaith hfNeg hreflected hgPath

/--
[rlc_axisCrossing_carrier_of_left_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_axisCrossing_carrier_of_left_contact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2}
  {k : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hfNeg : (rlc_dualReflect f) 0 < 0)
  (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]))
  (hgPath : rlc_dualReflect g ∈ rlc_pathVertices gamma'.1) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_axisCrossing_carrier_of_left_contact gamma gamma' hfaith hfNeg hreflected hgPath

/--
[rlc_reflectedLeft_opposite_continuation_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedLeft_opposite_continuation_carrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v b w h : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
  (hub : u ≠ b)
  (hvflip : rlc_dualReflect v = rlc_flipX w)
  (hw : w ∈ rlc_pathVertices gamma'.1)
  (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
  (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
  (hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect v = rlc_flipX r)
  (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 = 2 * (rlc_dualReflect v) 0 ∧ (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 = 2 * (rlc_dualReflect v) 1)
  (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_reflectedLeft_opposite_continuation_carrier gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft hvFlipRight hopp hvInterior hnotIn hhRegion hh

/--
[rlc_reflectedRight_opposite_continuation_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedRight_opposite_continuation_carrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v b w h : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
  (hub : u ≠ b)
  (hvflip : rlc_dualReflect v = rlc_flipX w)
  (hw : w ∈ rlc_pathVertices gamma.1)
  (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
  (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
  (hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1, rlc_dualReflect v = rlc_flipX r)
  (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 = 2 * (rlc_dualReflect v) 0 ∧ (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 = 2 * (rlc_dualReflect v) 1)
  (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_reflectedRight_opposite_continuation_carrier gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft hvFlipLeft hopp hvInterior hnotIn hhRegion hh

/--
[rlc_reflectedLeft_continuation_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedLeft_continuation_carrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v b w h : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
  (hub : u ≠ b)
  (hvflip : rlc_dualReflect v = rlc_flipX w)
  (hw : w ∈ rlc_pathVertices gamma'.1)
  (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
  (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
  (hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect v = rlc_flipX r)
  (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_reflectedLeft_continuation_carrier gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft hvFlipRight hvInterior hnotIn hhRegion hh

/--
[rlc_reflectedRight_continuation_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedRight_continuation_carrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v b w h : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
  (hub : u ≠ b)
  (hvflip : rlc_dualReflect v = rlc_flipX w)
  (hw : w ∈ rlc_pathVertices gamma.1)
  (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
  (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
  (hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1, rlc_dualReflect v = rlc_flipX r)
  (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_reflectedRight_continuation_carrier gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft hvFlipLeft hvInterior hnotIn hhRegion hh

/--
[rlc_positiveBarrier_continuation_or_right_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveBarrier_continuation_or_right_contact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v b h : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
  (hub : u ≠ b)
  (hvPos : 0 < (rlc_dualReflect v) 0)
  (hvBarrier : rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma')
  (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_positiveBarrier_continuation_or_right_contact gamma gamma' rho hno huv hvb hub hvPos hvBarrier hvInterior hnotIn hhRegion hh

/--
[rlc_negativeBarrier_continuation_or_left_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negativeBarrier_continuation_or_left_contact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v b h : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
  (hub : u ≠ b)
  (hvNeg : (rlc_dualReflect v) 0 < 0)
  (hvBarrier : rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma')
  (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_negativeBarrier_continuation_or_left_contact gamma gamma' rho hno huv hvb hub hvNeg hvBarrier hvInterior hnotIn hhRegion hh

/--
[rlc_positiveBarrier_bad_exit_forces_right_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveBarrier_bad_exit_forces_right_contact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {a u v : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hau : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj a u)
  (hauCarrier : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' a u)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hav : a ≠ v)
  (hnotWall : s(rlc_dualReflect a, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (huPos : 0 < (rlc_dualReflect u) 0)
  (huBarrier : rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma')
  (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧ (rlc_dualReflect u) 0 < 2 * n ∧ -n < (rlc_dualReflect u) 1 ∧ (rlc_dualReflect u) 1 < n)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  rlc_dualReflect u ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_positiveBarrier_bad_exit_forces_right_contact gamma gamma' rho hno hau hauCarrier huv hav hnotWall huPos huBarrier huInterior hbad

/--
[rlc_negativeBarrier_bad_exit_forces_left_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negativeBarrier_bad_exit_forces_left_contact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {a u v : Site 2}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hau : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj a u)
  (hauCarrier : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' a u)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hav : a ≠ v)
  (hnotWall : s(rlc_dualReflect a, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (huBarrier : rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma')
  (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧ (rlc_dualReflect u) 0 < 2 * n ∧ -n < (rlc_dualReflect u) 1 ∧ (rlc_dualReflect u) 1 < n)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  rlc_dualReflect u ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_negativeBarrier_bad_exit_forces_left_contact gamma gamma' rho hno hau hauCarrier huv hav hnotWall huNeg huBarrier huInterior hbad

/--
[rlc_reflectedLeft_rightBoundary_continuation_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedLeft_rightBoundary_continuation_carrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v b w h : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
  (hub : u ≠ b)
  (hvflip : rlc_dualReflect v = rlc_flipX w)
  (hw : w ∈ rlc_pathVertices gamma'.1)
  (hvRightBoundary : (rlc_dualReflect v) 0 = 2 * n)
  (hvBox : rlc_dualReflect v ∈ rlc_connectorBox n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_reflectedLeft_rightBoundary_continuation_carrier hn gamma gamma' hfaith rho hno huv hvb hub hvflip hw hvRightBoundary hvBox hnotIn hhRegion hh

/--
[rlc_reflectedLeft_bottomBoundary_continuation_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedLeft_bottomBoundary_continuation_carrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v b w h : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
  (hub : u ≠ b)
  (hvflip : rlc_dualReflect v = rlc_flipX w)
  (hw : w ∈ rlc_pathVertices gamma'.1)
  (hvBottom : (rlc_dualReflect v) 1 = -n)
  (hvBox : rlc_dualReflect v ∈ rlc_connectorBox n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_reflectedLeft_bottomBoundary_continuation_carrier hn gamma gamma' hfaith rho hno huv hvb hub hvflip hw hvBottom hvBox hnotIn hhRegion hh

/--
[rlc_reflectedEdgeCarrierGeometry_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedEdgeCarrierGeometry_comm_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2} :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ↔ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' g f := by
-- proof
  apply StatMech.Universality.rlc_reflectedEdgeCarrierGeometry_comm gamma gamma' f g

/--
[rlc_connectorCentralFaceGoodBoundaryGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_connectorCentralFaceGoodBoundaryGraph_le_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))} :
-- imply
  rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho ≤ faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho

/--
[RlcCentralFaceRetainedAnchoredBoundary.anchor_mem_goodBoundaryGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma anchor_mem_goodBoundaryGraph_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj B.firstFace B.secondFace := by
-- proof
  apply StatMech.Universality.RlcCentralFaceRetainedAnchoredBoundary.anchor_mem_goodBoundaryGraph B hfaith

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_axisEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma goodWalk_to_outsideAxis_reachableBarrier_or_axisEndpoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {N u v : Site 2}
  {k : Int}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk N u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hN : rlc_dualReflect N = (![-1, L.boundary.height + 1] : Site 2))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) = s((![-1, k] : Site 2), ![0, k]))
  (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨ (gamma'.1.2.1 : Site 2) 1 < k) :
-- imply
  (∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable N z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨ (![0, L.boundary.height + 1] : Site 2) ∈ rlc_connectorBarrier gamma gamma' ∨ (![0, k] : Site 2) ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_axisEndpoint L hfaith q hN huNeg hreflected hkOutside

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.negativeAnchor_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma negativeAnchor_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {N : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hN : rlc_dualReflect N = (![-1, L.boundary.height + 1] : Site 2)) :
-- imply
  (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace N := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.negativeAnchor_reachable L hfaith hN

/--
[rlc_goodBoundary_reachable_dualReflect_mem_box_of_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_reachable_dualReflect_mem_box_of_start_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x z : Site 2}
-- given
  (hx : rlc_dualReflect x ∈ rlc_connectorBox n)
  (hz : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable x z) :
-- imply
  rlc_dualReflect z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_reachable_dualReflect_mem_box_of_start hx hz

/--
[rlc_goodBoundary_reachable_dualReflect_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_reachable_dualReflect_mem_box_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hz : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace z) :
-- imply
  rlc_dualReflect z ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_reachable_dualReflect_mem_box B hfaith hz

/--
[rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ A : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace A ∧ (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable A B.firstFace ∧ rlc_dualReflect A = (![0, B.height + 1] : Site 2) ∧ (rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∨ rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier B hfaith

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.axisAnchor_barrier_forces_reachable_left_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma axisAnchor_barrier_forces_reachable_left_contact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbarrier : (![0, L.boundary.height + 1] : Site 2) ∈ rlc_connectorBarrier gamma gamma') :
-- imply
  ∃ A : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace A ∧ rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.axisAnchor_barrier_forces_reachable_left_contact L hfaith hbarrier

/--
[rlc_faithful_axisOutside_barrier_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_faithful_axisOutside_barrier_classify_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {k : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbarrier : (![0, k] : Site 2) ∈ rlc_connectorBarrier gamma gamma') :
-- imply
  (k ≤ (gamma.1.1 : Site 2) 1 → (![0, k] : Site 2) ∈ rlc_pathVertices gamma.1) ∧ ((gamma'.1.2.1 : Site 2) 1 < k → False) := by
-- proof
  apply StatMech.Universality.rlc_faithful_axisOutside_barrier_classify gamma gamma' hfaith hbarrier

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma goodWalk_to_outsideAxis_reachableBarrier_or_contact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {N u v : Site 2}
  {k : Int}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk N u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hN : rlc_dualReflect N = (![-1, L.boundary.height + 1] : Site 2))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) = s((![-1, k] : Site 2), ![0, k]))
  (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨ (gamma'.1.2.1 : Site 2) 1 < k) :
-- imply
  (∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨ (∃ A : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace A ∧ rlc_dualReflect A ∈ rlc_pathVertices gamma'.1) ∨ rlc_dualReflect v ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_contact L hfaith q hN huNeg hreflected hkOutside

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {N u v : Site 2}
  {k : Int}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk N u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hN : rlc_dualReflect N = (![-1, L.boundary.height + 1] : Site 2))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) = s((![-1, k] : Site 2), ![0, k]))
  (hkOutside : k ≤ (gamma.1.1 : Site 2) 1 ∨ (gamma'.1.2.1 : Site 2) 1 < k) :
-- imply
  (∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨ (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ ∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_outsideAxis_reachableBarrier_or_reachableContact L hfaith q hN huNeg huv hreflected hkOutside

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_extremeAxis_reachableBarrier_contact_or_higherAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma goodWalk_to_extremeAxis_reachableBarrier_contact_or_higherAxis_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {N u v : Site 2}
  {k : Int}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk N u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hN : rlc_dualReflect N = (![-1, L.boundary.height + 1] : Site 2))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hreflected : s(rlc_dualReflect u, rlc_dualReflect v) = s((![-1, k] : Site 2), ![0, k]))
  (hkExtreme : k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k) :
-- imply
  (∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨ (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ ∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x = (![0, k] : Site 2) ∧ L.boundary.height + 1 < k ∧ k ≤ (gamma'.1.2.1 : Site 2) 1 := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.goodWalk_to_extremeAxis_reachableBarrier_contact_or_higherAxis L hfaith q hN huNeg huv hreflected hkExtreme

/--
[rlc_goodBoundary_walk_to_boxBoundary_meets_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_walk_to_boxBoundary_meets_barrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {A u : Site 2}
  {pGood : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAzero : rlc_dualReflect A = (![0, B.height + 1] : Site 2))
  (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) :
-- imply
  ∃ z ∈ pGood.support, rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_walk_to_boxBoundary_meets_barrier B hfaith pGood hAzero huBoundary

/--
[rlc_goodBoundary_barrier_hit_before_boxBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_barrier_hit_before_boxBoundary_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace u)
  (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) :
-- imply
  ∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_barrier_hit_before_boxBoundary B hfaith hu huBoundary

/--
[rlc_goodBoundary_reachable_wall_or_region_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_reachable_wall_or_region_incident_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hz : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace z) :
-- imply
  rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' ∨ ∃ w : Site 2, (hypercubicLattice 2).Adj (rlc_dualReflect z) (rlc_dualReflect w) ∧ rlc_dualReflect w ∈ rlc_connectorBox n ∧ ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma', h ∈ flankFaces (rlc_dualReflect z) (rlc_dualReflect w) := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_reachable_wall_or_region_incident B hfaith hz

/--
[rlc_goodBoundary_reachable_wall_or_region_incident_of_barrier_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_reachable_wall_or_region_incident_of_barrier_start_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x z : Site 2}
-- given
  (hxBarrier : rlc_dualReflect x ∈ rlc_connectorBarrier gamma gamma')
  (hz : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable x z) :
-- imply
  rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' ∨ ∃ w : Site 2, (hypercubicLattice 2).Adj (rlc_dualReflect z) (rlc_dualReflect w) ∧ rlc_dualReflect w ∈ rlc_connectorBox n ∧ ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma', h ∈ flankFaces (rlc_dualReflect z) (rlc_dualReflect w) := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_reachable_wall_or_region_incident_of_barrier_start hxBarrier hz

/--
[rlc_walk_subgraph_prefix_or_first_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_walk_subgraph_prefix_or_first_exit_eq
  [DecidableEq V]
  {G H : SimpleGraph V}
  {x y : V}
  {w : H.Walk x y} :
-- imply
  (∃ q : G.Walk x y, ∀ e ∈ q.edges, e ∈ w.edges) ∨ ∃ (u v : V) (q : G.Walk x u), H.Adj u v ∧ s(u, v) ∈ w.edges ∧ ¬ G.Adj u v ∧ ∀ e ∈ q.edges, e ∈ w.edges := by
-- proof
  apply StatMech.Universality.rlc_walk_subgraph_prefix_or_first_exit w

/--
[rlc_walk_subgraph_exact_or_first_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_walk_subgraph_exact_or_first_exit_eq
  [DecidableEq V]
  {G H : SimpleGraph V}
  {x y : V}
  {w : H.Walk x y} :
-- imply
  (∃ q : G.Walk x y, q.edges = w.edges) ∨ ∃ (u v : V) (q : G.Walk x u), H.Adj u v ∧ s(u, v) ∈ w.edges ∧ ¬ G.Adj u v ∧ ∀ e ∈ q.edges, e ∈ w.edges := by
-- proof
  apply StatMech.Universality.rlc_walk_subgraph_exact_or_first_exit w

/--
[rlc_walk_subgraph_lift_or_first_exit_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_walk_subgraph_lift_or_first_exit_decomp_eq
  {G H : SimpleGraph V}
  {x y : V}
  {w : H.Walk x y}
-- given
  (hle : G ≤ H) :
-- imply
  (∃ q : G.Walk x y, q.mapLe hle = w) ∨ ∃ (u v : V) (q : G.Walk x u) (r : H.Walk v y) (huv : H.Adj u v), ¬ G.Adj u v ∧ w = (q.mapLe hle).append (.cons huv r) := by
-- proof
  apply StatMech.Universality.rlc_walk_subgraph_lift_or_first_exit_decomp hle w

/--
[rlc_goodBoundary_prefix_or_first_bad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_prefix_or_first_bad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : Site 2}
  {w : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk x y} :
-- imply
  (∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk x y, ∀ e ∈ q.edges, e ∈ w.edges) ∨ ∃ (u v : Site 2) (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk x u), (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧ s(u, v) ∈ w.edges ∧ ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧ ∀ e ∈ q.edges, e ∈ w.edges := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_prefix_or_first_bad w

/--
[rlc_goodBoundary_exact_or_first_bad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_exact_or_first_bad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : Site 2}
  {w : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk x y} :
-- imply
  (∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk x y, q.edges = w.edges) ∨ ∃ (u v : Site 2) (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk x u), (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧ s(u, v) ∈ w.edges ∧ ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧ ∀ e ∈ q.edges, e ∈ w.edges := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_exact_or_first_bad w

/--
[rlc_goodBoundary_lift_or_first_bad_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_lift_or_first_bad_decomp_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x y : Site 2}
  {w : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk x y} :
-- imply
  (∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk x y, q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho) = w) ∨ ∃ (u v : Site 2) (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk x u) (r : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v y) (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v), ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧ w = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons huv r) := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_lift_or_first_bad_decomp w

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_axis_crossing_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma twoBadMiddle_axis_crossing_extreme_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {r : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v L.boundary.secondFace}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
  {t : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v}
-- given
  (haExact : ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
  (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hdecomp : a = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons huv r))
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hdecomp' : r.reverse = (q'.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons hu'v' t))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hu'Pos : 0 < (rlc_dualReflect u') 0) :
-- imply
  ∃ (f g : Site 2) (k : Int), s(f, g) ∈ L.boundary.contour.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]) ∧ (k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_axis_crossing_extreme L haExact haAvoid q r huv hdecomp q' t hu'v' hdecomp' huNeg hu'Pos

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.goodContourEdge_location_twoBadMiddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma goodContourEdge_location_twoBadMiddle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {r : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v L.boundary.secondFace}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
  {t : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v}
  {f g : Site 2}
-- given
  (haExact : ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hdecomp : a = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons huv r))
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
  (hdecomp' : r.reverse = (q'.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons hu'v' t))
  (hfgContour : s(f, g) ∈ L.boundary.contour.edges)
  (hfgGood : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g) :
-- imply
  s(f, g) = s(L.boundary.firstFace, L.boundary.secondFace) ∨ s(f, g) ∈ q.edges ∨ s(f, g) ∈ q'.edges ∨ s(f, g) ∈ t.edges := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.goodContourEdge_location_twoBadMiddle L haExact q r huv hbad hdecomp q' t hu'v' hbad' hdecomp' hfgContour hfgGood

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.goodContourEdge_mem_middle_of_avoids_anchor_prefixes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma goodContourEdge_mem_middle_of_avoids_anchor_prefixes_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {r : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v L.boundary.secondFace}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
  {t : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v}
  {f g : Site 2}
-- given
  (haExact : ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hdecomp : a = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons huv r))
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
  (hdecomp' : r.reverse = (q'.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons hu'v' t))
  (hfgContour : s(f, g) ∈ L.boundary.contour.edges)
  (hfgGood : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g)
  (havoidAnchor : s(f, g) ≠ s(L.boundary.firstFace, L.boundary.secondFace))
  (havoidQ : s(f, g) ∉ q.edges)
  (havoidQ' : s(f, g) ∉ q'.edges) :
-- imply
  s(f, g) ∈ t.edges := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.goodContourEdge_mem_middle_of_avoids_anchor_prefixes L haExact q r huv hbad hdecomp q' t hu'v' hbad' hdecomp' hfgContour hfgGood havoidAnchor havoidQ havoidQ'

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.complementaryPath_good_or_two_bad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma complementaryPath_good_or_two_bad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho} :
-- imply
  ∃ a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace, a.IsPath ∧ (∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges) ∧ ((∃ q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace L.boundary.secondFace, q.edges = a.edges) ∨ ∃ (u v u' v' : Site 2) (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u) (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'), (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧ s(u, v) ∈ a.edges ∧ ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v' ∧ s(u', v') ∈ a.edges ∧ ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v') := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.complementaryPath_good_or_two_bad L

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.reachableFaithfulContacts_of_complementaryPath_good](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma reachableFaithfulContacts_of_complementaryPath_good_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace L.boundary.secondFace}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (haExact : ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
  (hqEdges : q.edges = a.edges) :
-- imply
  ∃ x y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable x y ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.reachableFaithfulContacts_of_complementaryPath_good L hfaith hno haExact q hqEdges

/--
[rlc_goodBoundary_first_barrier_incoming_region_flank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_first_barrier_incoming_region_flank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {A z : Site 2}
  {p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A z}
-- given
  (hA : rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma')
  (hz : rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') :
-- imply
  ∃ (u v : Site 2) (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A u), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj u v ∧ s(u, v) ∈ p.edges ∧ (∀ e ∈ q.edges, e ∈ p.edges) ∧ (∀ w ∈ q.support, rlc_dualReflect w ∉ rlc_connectorBarrier gamma gamma') ∧ rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma' ∧ s(rlc_dualReflect u, rlc_dualReflect v) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ rlc_dualReflect u ∈ rlc_connectorBox n ∧ rlc_dualReflect v ∈ rlc_connectorBox n ∧ ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma', h ∈ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_first_barrier_incoming_region_flank p hA hz

/--
[rlc_goodBoundary_first_barrier_contact_boundary_or_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_first_barrier_contact_boundary_or_extend_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {A z : Site 2}
  {p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A z}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hA : rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma')
  (hz : rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') :
-- imply
  ∃ (u v b : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable A v ∧ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b ∧ u ≠ b ∧ rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma' ∧ (rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨ ¬ (-2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n) ∨ (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj v b) := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_first_barrier_contact_boundary_or_extend hno p hA hz

/--
[rlc_goodBoundary_first_bad_toward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_first_bad_toward_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {z : Site 2}
-- given
  (hz : z ∈ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support)
  (hzNot : ¬ (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace z) :
-- imply
  ∃ u v : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace u ∧ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧ ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧ ¬ (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace v := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_first_bad_toward B hz hzNot

/--
[rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x u v : Site 2}
-- given
  (hxBarrier : rlc_dualReflect x ∈ rlc_connectorBarrier gamma gamma')
  (hxBox : rlc_dualReflect x ∈ rlc_connectorBox n)
  (hu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable x u)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧ (rlc_dualReflect u) 0 < 2 * n ∧ -n < (rlc_dualReflect u) 1 ∧ (rlc_dualReflect u) 1 < n) :
-- imply
  rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start hxBarrier hxBox hu huv hbad huInterior

/--
[rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace u)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧ (rlc_dualReflect u) 0 < 2 * n ∧ -n < (rlc_dualReflect u) 1 ∧ (rlc_dualReflect u) 1 < n) :
-- imply
  rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_bad_exit_near_mem_barrier_of_interior B hfaith hu huv hbad huInterior

/--
[rlc_badExit_interior_nonwall_box_noCentralFlank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_badExit_interior_nonwall_box_noCentralFlank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {u v : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧ (rlc_dualReflect u) 0 < 2 * n ∧ -n < (rlc_dualReflect u) 1 ∧ (rlc_dualReflect u) 1 < n)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  s(rlc_dualReflect u, rlc_dualReflect v) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ rlc_dualReflect u ∈ rlc_connectorBox n ∧ rlc_dualReflect v ∈ rlc_connectorBox n ∧ ∀ h ∈ rlc_connectorCentralFaceRegion gamma gamma', h ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
-- proof
  apply StatMech.Universality.rlc_badExit_interior_nonwall_box_noCentralFlank huv huInterior hbad

/--
[rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace u)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨ (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary B hfaith hu huv hbad

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace u)
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ ((rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) ∨ ∃ w ∈ rlc_pathVertices gamma.1, rlc_dualReflect u = rlc_flipX w ∧ ∀ a : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u → a ≠ v → s(rlc_dualReflect a, rlc_dualReflect u) ∈ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall L hfaith hno hu huNeg huv hbad

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace u)
  (huPos : 0 < (rlc_dualReflect u) 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ ((rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) ∨ ∃ w ∈ rlc_pathVertices gamma'.1, rlc_dualReflect u = rlc_flipX w ∧ ∀ a : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u → a ≠ v → s(rlc_dualReflect a, rlc_dualReflect u) ∈ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall L hfaith hno hu huPos huv hbad

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExit_reachable_left_or_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma negativeBadExit_reachable_left_or_barrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace u)
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ ∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExit_reachable_left_or_barrier L hfaith hno hu huNeg huv hbad

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExit_reachable_right_or_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveBadExit_reachable_right_or_barrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace u)
  (huPos : 0 < (rlc_dualReflect u) 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ ∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExit_reachable_right_or_barrier L hfaith hno hu huPos huv hbad

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_reachable_or_negativeBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma complementary_first_axis_crossing_reachable_or_negativeBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  (∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨ (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ (∃ (x : Site 2) (k : Int), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x = (![0, k] : Site 2) ∧ L.boundary.height + 1 < k ∧ k ≤ (gamma'.1.2.1 : Site 2) 1) ∨ ∃ u v : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace u ∧ (rlc_dualReflect u) 0 < 0 ∧ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧ s(u, v) ∈ L.boundary.contour.edges ∧ ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧ (rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨ (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_reachable_or_negativeBad L hfaith

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_reachableBarrier_contact_or_higherAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma complementary_first_axis_crossing_reachableBarrier_contact_or_higherAxis_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  (∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∨ (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ ∃ (x : Site 2) (k : Int), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x = (![0, k] : Site 2) ∧ L.boundary.height + 1 < k ∧ k ≤ (gamma'.1.2.1 : Site 2) 1 := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_reachableBarrier_contact_or_higherAxis L hfaith hno

/--
[rlc_goodBoundary_walk_barrier_before_bad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_walk_barrier_before_bad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {A u v : Site 2}
  {pA : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A B.firstFace}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk B.firstFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAzero : rlc_dualReflect A = (![0, B.height + 1] : Site 2))
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  ∃ z ∈ (pA.append q).support, rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_walk_barrier_before_bad B hfaith pA q hAzero huv hbad

/--
[rlc_goodBoundary_barrier_hit_before_first_bad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodBoundary_barrier_hit_before_first_bad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hz : z ∈ (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).support)
  (hzNot : ¬ (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace z) :
-- imply
  ∃ u : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace u ∧ rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_goodBoundary_barrier_hit_before_first_bad B hfaith hz hzNot

/--
[rlc_goodComponentContacts_or_badCarrierSeparation_of_filledContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_badCarrierSeparation_of_filledContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hcontacts : RlcCentralFaceFilledBoundaryContacts gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryBadCarrierSeparation gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_badCarrierSeparation_of_filledContacts gamma gamma' rho hcontacts

/--
[rlc_goodComponentContacts_or_badCarrierSeparation_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_badCarrierSeparation_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryBadCarrierSeparation gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_badCarrierSeparation_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_goodComponentContacts_or_classifiedBadCarrierSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_classifiedBadCarrierSeparation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparation gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparation gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_classifiedBadCarrierSeparation gamma gamma' rho hsep

/--
[rlc_goodComponentContacts_or_classifiedBadCarrierSeparation_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_classifiedBadCarrierSeparation_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparation gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_classifiedBadCarrierSeparation_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_goodComponentContacts_or_badCarrierSeparationFromLeft_of_filledContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_badCarrierSeparationFromLeft_of_filledContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hcontacts : RlcCentralFaceFilledBoundaryContacts gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryBadCarrierSeparationFromLeft gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_badCarrierSeparationFromLeft_of_filledContacts gamma gamma' rho hcontacts

/--
[rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparationFromLeft gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparationFromLeft gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft gamma gamma' rho hsep

/--
[rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparationFromLeft gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_badExit_exists_incomingWall_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_badExit_exists_incomingWall_of_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x u v : Site 2}
-- given
  (hxu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable x u)
  (hxuNe : x ≠ u)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hwall : RlcCentralFaceBadExitAllIncomingWall gamma gamma' rho u v) :
-- imply
  ∃ a : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u ∧ a ≠ v ∧ s(rlc_dualReflect a, rlc_dualReflect u) ∈ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_badExit_exists_incomingWall_of_reachable hxu hxuNe hbad hwall

/--
[rlc_rightBased_negative_badExit_incoming_reflectedRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_rightBased_negative_badExit_incoming_reflectedRight_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {x u v : Site 2}
-- given
  (hnoGood : ¬ RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hxu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable x u)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hwall : RlcCentralFaceBadExitAllIncomingWall gamma gamma' rho u v) :
-- imply
  ∃ a : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u ∧ a ≠ v ∧ s(rlc_dualReflect a, rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_rightBased_negative_badExit_incoming_reflectedRight gamma gamma' rho hnoGood hxPath hxu hbad huNeg hwall

/--
[rlc_leftBased_positive_badExit_incoming_reflectedLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_leftBased_positive_badExit_incoming_reflectedLeft_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {y u v : Site 2}
-- given
  (hnoGood : ¬ RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable y u)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (huPos : 0 < (rlc_dualReflect u) 0)
  (hwall : RlcCentralFaceBadExitAllIncomingWall gamma gamma' rho u v) :
-- imply
  ∃ a : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u ∧ a ≠ v ∧ s(rlc_dualReflect a, rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_leftBased_positive_badExit_incoming_reflectedLeft gamma gamma' rho hnoGood hyPath hyu hbad huPos hwall

/--
[rlc_goodComponentContacts_or_reducedBadCarrierSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_reducedBadCarrierSeparation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparation gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryReducedBadCarrierSeparation gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_reducedBadCarrierSeparation gamma gamma' rho hno hsep

/--
[rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparationFromLeft gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryReducedBadCarrierSeparationFromLeft gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft gamma gamma' rho hno hsep

/--
[rlc_goodComponentContacts_or_reducedBadCarrierSeparation_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_reducedBadCarrierSeparation_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryReducedBadCarrierSeparation gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_reducedBadCarrierSeparation_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceFilledBoundaryReducedBadCarrierSeparationFromLeft gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_goodComponentContacts_or_twoSidedReducedBadCarrierSeparation_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_twoSidedReducedBadCarrierSeparation_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ (RlcCentralFaceFilledBoundaryReducedBadCarrierSeparation gamma gamma' rho ∧ RlcCentralFaceFilledBoundaryReducedBadCarrierSeparationFromLeft gamma gamma' rho) := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_twoSidedReducedBadCarrierSeparation_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_goodComponentContacts_or_lowestAnchorOrderedBadExit_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_lowestAnchorOrderedBadExit_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceLowestAnchorOrderedBadExit gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_lowestAnchorOrderedBadExit_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_goodComponentContacts_or_lowestAnchor_lower_or_upper_orderBadExit_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_lowestAnchor_lower_or_upper_orderBadExit_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceLowestAnchorLowerOrderBadExit gamma gamma' rho ∨ RlcCentralFaceLowestAnchorUpperOrderBadExit gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_lowestAnchor_lower_or_upper_orderBadExit_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_goodComponentContacts_of_anchoredGoodComponentContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_of_anchoredGoodComponentContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hcomponent : RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_of_anchoredGoodComponentContacts gamma gamma' rho hcomponent

/--
[rlc_anchoredGoodComponentContacts_or_reachableBarrier_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_anchoredGoodComponentContacts_or_reachableBarrier_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts gamma gamma' rho ∨ ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) (z : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_anchoredGoodComponentContacts_or_reachableBarrier_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_anchoredGoodComponentContacts_or_reachableClassifiedBarrier_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_anchoredGoodComponentContacts_or_reachableClassifiedBarrier_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts gamma gamma' rho ∨ ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) (z : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace z ∧ (rlc_dualReflect z ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect z ∈ rlc_pathVertices gamma'.1 ∨ (0 < (rlc_dualReflect z) 0 ∧ ∃ w ∈ rlc_pathVertices gamma'.1, rlc_dualReflect z = rlc_flipX w) ∨ ((rlc_dualReflect z) 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1, rlc_dualReflect z = rlc_flipX w)) := by
-- proof
  apply StatMech.Universality.rlc_anchoredGoodComponentContacts_or_reachableClassifiedBarrier_of_faithful_failure gamma gamma' hfaith rho hno

/--
[rlc_anchorToFaithfulContacts_reachable_or_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_anchorToFaithfulContacts_reachable_or_barrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
-- imply
  ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) (x y : Site 2), rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ ((rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace x ∨ ∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∧ ((rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace y ∨ ∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_anchorToFaithfulContacts_reachable_or_barrier gamma gamma' hfaith rho hno

/--
[rlc_anchoredSupportedSide_of_anchoredGeometricSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_anchoredSupportedSide_of_anchoredGeometricSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hgeom : RlcCentralFaceFilledBoundaryAnchoredGeometricSide gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryAnchoredSupportedSide gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_anchoredSupportedSide_of_anchoredGeometricSide gamma gamma' rho hgeom

/--
[rlc_filledBoundaryContactSegment_of_anchoredGoodComponentContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_filledBoundaryContactSegment_of_anchoredGoodComponentContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hcomponent : RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_filledBoundaryContactSegment_of_anchoredGoodComponentContacts gamma gamma' rho hcomponent

/--
[rlc_filledBoundaryContactSegment_of_goodComponentContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_filledBoundaryContactSegment_of_goodComponentContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hcomponent : RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_filledBoundaryContactSegment_of_goodComponentContacts gamma gamma' rho hcomponent

/--
[rlc_filledBoundaryContactSegment_of_anchoredSupportedSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_filledBoundaryContactSegment_of_anchoredSupportedSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hside : RlcCentralFaceFilledBoundaryAnchoredSupportedSide gamma gamma' rho) :
-- imply
  RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_filledBoundaryContactSegment_of_anchoredSupportedSide gamma gamma' rho hside

/--
[rlc_boundaryContactArc_of_filledBoundaryContactSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_boundaryContactArc_of_filledBoundaryContactSegment_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hsegment : RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho) :
-- imply
  RlcCentralFaceBoundaryContactArc gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_boundaryContactArc_of_filledBoundaryContactSegment gamma gamma' rho hsegment

/--
[rlc_centralFacePIMS_success_of_filledBoundaryContactSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_success_of_filledBoundaryContactSegment_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hsegment : RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho) :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_success_of_filledBoundaryContactSegment gamma gamma' rho hsegment

/--
[rlc_centralFacePIMS_success_of_anchoredGoodComponentContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_success_of_anchoredGoodComponentContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hcomponent : RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts gamma gamma' rho) :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_success_of_anchoredGoodComponentContacts gamma gamma' rho hcomponent

/--
[rlc_centralFacePIMS_success_of_goodComponentContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_success_of_goodComponentContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hcomponent : RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho) :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_success_of_goodComponentContacts gamma gamma' rho hcomponent

/--
[rlc_centralFacePIMS_success_of_anchoredGeometricSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_success_of_anchoredGeometricSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hgeom : RlcCentralFaceFilledBoundaryAnchoredGeometricSide gamma gamma' rho) :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_success_of_anchoredGeometricSide gamma gamma' rho hgeom

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_exactResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma twoSignedBadExits_PIMS_or_exactResidue_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hu'Pos : 0 < (rlc_dualReflect u') 0) :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨ RlcCentralFaceNegativeBadExitResidue gamma gamma' rho u v ∨ RlcCentralFacePositiveBadExitResidue gamma gamma' rho u' v' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_exactResidue L hfaith hno q q' huv hbad hu'v' hbad' huNeg hu'Pos

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_reachableBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma twoSignedBadExits_PIMS_or_reachableBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hu'Pos : 0 < (rlc_dualReflect u') 0) :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨ ∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_reachableBarrier L hfaith hno q q' huv hbad hu'v' hbad' huNeg hu'Pos

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_PIMS_or_reachableBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma twoBadMiddle_extreme_and_PIMS_or_reachableBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {r : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v L.boundary.secondFace}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
  {t : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v}
-- given
  (haExact : ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
  (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hdecomp : a = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons huv r))
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
  (hdecomp' : r.reverse = (q'.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons hu'v' t))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hu'Pos : 0 < (rlc_dualReflect u') 0) :
-- imply
  (∃ (f g : Site 2) (k : Int), s(f, g) ∈ L.boundary.contour.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]) ∧ (k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k)) ∧ (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨ ∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_PIMS_or_reachableBarrier L haExact haAvoid hfaith hno q r huv hbad hdecomp q' t hu'v' hbad' hdecomp' huNeg hu'Pos

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_PIMS_or_exactResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma twoBadMiddle_extreme_and_PIMS_or_exactResidue_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {r : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v L.boundary.secondFace}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
  {t : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v}
-- given
  (haExact : ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
  (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hdecomp : a = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons huv r))
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
  (hdecomp' : r.reverse = (q'.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons hu'v' t))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hu'Pos : 0 < (rlc_dualReflect u') 0) :
-- imply
  (∃ (f g : Site 2) (k : Int), s(f, g) ∈ L.boundary.contour.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]) ∧ (k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k)) ∧ (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨ RlcCentralFaceNegativeBadExitResidue gamma gamma' rho u v ∨ RlcCentralFacePositiveBadExitResidue gamma gamma' rho u' v') := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_PIMS_or_exactResidue L haExact haAvoid hfaith hno q r huv hbad hdecomp q' t hu'v' hbad' hdecomp' huNeg hu'Pos

/--
[rlc_bookFlippedTraceIntersectionSet_nonempty_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_bookFlippedTraceIntersectionSet_nonempty_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  (rlc_bookFlippedTraceIntersectionSet gamma gamma').Nonempty := by
-- proof
  apply StatMech.Universality.rlc_bookFlippedTraceIntersectionSet_nonempty_of_faithful gamma gamma' hfaith

/--
[rlc_exists_first_bookFlippedTraceIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_exists_first_bookFlippedTraceIntersection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ z : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'), ∀ q : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'), rlc_bookFlippedTraceIntersectionRank gamma gamma' z ≤ rlc_bookFlippedTraceIntersectionRank gamma gamma' q := by
-- proof
  apply StatMech.Universality.rlc_exists_first_bookFlippedTraceIntersection gamma gamma' hfaith

/--
[rlc_bookFirstFlippedTraceIntersection_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_bookFirstFlippedTraceIntersection_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  let W := rlc_ambientCrossingWalk gamma.1 ∃ (z : Site 2) (hzW : z ∈ W.support), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ (∀ q ∈ (W.takeUntil z hzW).support, rlc_flipX q ∈ rlc_pathVertices gamma'.1 → q = z) ∧ ∀ q (hqW : q ∈ W.support), rlc_flipX q ∈ rlc_pathVertices gamma'.1 → (W.takeUntil z hzW).length ≤ (W.takeUntil q hqW).length := by
-- proof
  apply StatMech.Universality.rlc_bookFirstFlippedTraceIntersection_of_faithful gamma gamma' hfaith

/--
[rlc_ambientCrossingWalk_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_ambientCrossingWalk_isPath_eq
  {a b c d : Int}
  {tau : RlcCrossingPath a b c d} :
-- imply
  (rlc_ambientCrossingWalk tau).IsPath := by
-- proof
  apply StatMech.Universality.rlc_ambientCrossingWalk_isPath tau

/--
[rlc_isPath_start_not_mem_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_isPath_start_not_mem_tail_eq
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath) :
-- imply
  u ∉ p.support.tail := by
-- proof
  apply StatMech.Universality.rlc_isPath_start_not_mem_tail hp

/--
[rlc_append_isPath_of_endpoint_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_append_isPath_of_endpoint_intersection_eq
  {G : SimpleGraph V}
  {u v w : V}
  {p : G.Walk u v}
  {q : G.Walk v w}
-- given
  (hp : p.IsPath)
  (hq : q.IsPath)
  (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
-- imply
  (p.append q).IsPath := by
-- proof
  apply StatMech.Universality.rlc_append_isPath_of_endpoint_intersection hp hq hinter

/--
[rlc_append_isCycle_of_endpoint_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_append_isCycle_of_endpoint_intersection_eq
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
  {q : G.Walk v u}
-- given
  (hp : p.IsPath)
  (hq : q.IsPath)
  (huv : u ≠ v)
  (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v)
  (hedges : p.edges.Disjoint q.edges) :
-- imply
  (p.append q).IsCycle := by
-- proof
  apply StatMech.Universality.rlc_append_isCycle_of_endpoint_intersection hp hq huv hinter hedges

/--
[rlc_isPath_idxOf_le_of_mem_dropUntil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_isPath_idxOf_le_of_mem_dropUntil_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b z q : V}
  {W : G.Walk a b}
-- given
  (hW : W.IsPath)
  (hz : z ∈ W.support)
  (hq : q ∈ (W.dropUntil z hz).support) :
-- imply
  W.support.idxOf z ≤ W.support.idxOf q := by
-- proof
  apply StatMech.Universality.rlc_isPath_idxOf_le_of_mem_dropUntil W hW hz hq

/--
[rlc_bookFirstIntersection_truncatedSides_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_bookFirstIntersection_truncatedSides_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ (z : Site 2) (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) (left : (hypercubicLattice 2).Walk (rlc_flipX z) (gamma'.1.2.1 : Site 2)) (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) (preFlipLeft : (hypercubicLattice 2).Walk (rlc_flipX (gamma'.1.1 : Site 2)) z), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ (∀ e ∈ right.edges, e ∈ rlc_pathEdges gamma.1) ∧ (∀ e ∈ left.edges, e ∈ rlc_pathEdges gamma'.1) ∧ (∀ e ∈ flipLeft.edges, e ∈ rlc_reflectedPathEdges gamma'.1) ∧ (∀ x ∈ right.support, x ∈ flipLeft.support → x = z) ∧ (∀ x : Site 2, x ∈ flipLeft.support ↔ rlc_flipX x ∈ left.support) ∧ (∀ x ∈ flipLeft.support, (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤ (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX x)) ∧ (∀ x ∈ preFlipLeft.support, x ∈ right.support → x = z) ∧ (∀ x ∈ preFlipLeft.support, x ∈ flipLeft.support → x = z) ∧ (∀ x ∈ preFlipLeft.support, x ≠ z → 0 < x 0) ∧ right.IsPath ∧ left.IsPath ∧ flipLeft.IsPath ∧ preFlipLeft.IsPath ∧ (∀ e ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).edges, e ∈ preFlipLeft.edges ∨ e ∈ flipLeft.edges) ∧ (right.append flipLeft).IsPath ∧ right.length = (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧ ∀ q (hq : q ∈ rlc_pathVertices gamma.1), rlc_flipX q ∈ rlc_pathVertices gamma'.1 → right.length ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf q := by
-- proof
  apply StatMech.Universality.rlc_bookFirstIntersection_truncatedSides_of_faithful gamma gamma' hfaith

/--
[rlc_bookFirstIntersectionFourTraceAxisCycle_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_bookFirstIntersectionFourTraceAxisCycle_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ (c : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)), c.IsCycle ∧ (gamma.1.1 : Site 2) ∈ c.support ∧ (gamma'.1.2.1 : Site 2) ∈ c.support ∧ (∀ e ∈ c.edges, e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧ (∀ k : Int, (gamma.1.1 : Site 2) 1 < k → k ≤ (gamma'.1.2.1 : Site 2) 1 → ¬ Even (jec_rayCount (![1, k] : Site 2) c)) ∧ ∀ {x y : Site 2}, s(x, y) ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).edges → s(x, y) ∈ c.edges ∨ ∀ h ∈ flankFaces x y, phb_doubleDualEquiv.symm h ∉ jec_leftRegion c := by
-- proof
  apply StatMech.Universality.rlc_bookFirstIntersectionFourTraceAxisCycle_of_faithful gamma gamma' hfaith

/--
[rlc_cycleEdge_oppositeFlank_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_cycleEdge_oppositeFlank_outside_eq
  {a x y h k : Site 2}
  {c : (hypercubicLattice 2).Walk a a}
-- given
  (hcycle : c.IsCycle)
  (hxy : (hypercubicLattice 2).Adj x y)
  (hflank : flankFaces x y = s(h, k))
  (hedge : s(x, y) ∈ c.edges)
  (hhInside : phb_doubleDualEquiv.symm h ∈ jec_leftRegion c) :
-- imply
  phb_doubleDualEquiv.symm k ∉ jec_leftRegion c := by
-- proof
  apply StatMech.Universality.rlc_cycleEdge_oppositeFlank_outside hcycle hxy hflank hedge hhInside

/--
[rlc_centralRegion_inside_firstIntersectionCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralRegion_inside_firstIntersectionCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ (c : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)), c.IsCycle ∧ (∀ e ∈ c.edges, e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧ (∀ h ∈ rlc_connectorCentralFaceRegion gamma gamma', phb_doubleDualEquiv.symm h ∈ jec_leftRegion c) ∧ ∀ {x y : Site 2}, s(x, y) ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).edges → s(x, y) ∈ c.edges ∨ ∀ h ∈ flankFaces x y, phb_doubleDualEquiv.symm h ∉ jec_leftRegion c := by
-- proof
  apply StatMech.Universality.rlc_centralRegion_inside_firstIntersectionCycle gamma gamma' hfaith

/--
[rlc_walk_all_edges_or_last_failure_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_walk_all_edges_or_last_failure_decomp_eq
  {G : SimpleGraph V}
  {x y : V}
  {w : G.Walk x y}
-- given
  (P : Sym2 V → Prop) :
-- imply
  (∀ e ∈ w.edges, P e) ∨ ∃ (u v : V) (p : G.Walk x u) (r : G.Walk v y) (huv : G.Adj u v), ¬ P s(u, v) ∧ (∀ e ∈ r.edges, P e) ∧ w = p.append (.cons huv r) := by
-- proof
  apply StatMech.Universality.rlc_walk_all_edges_or_last_failure_decomp P w

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExitResidue_left_boundary_or_wallRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma negativeBadExitResidue_left_boundary_or_wallRun_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hresidue : RlcCentralFaceNegativeBadExitResidue gamma gamma' rho u v) :
-- imply
  (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ ((rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) ∨ RlcCentralFaceNegativeWallRunSurgeryAt gamma gamma' rho L u := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExitResidue_left_boundary_or_wallRun L hfaith q huNeg huv hbad hresidue

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExitResidue_boundary_or_axisWallRun_or_lastWallRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveBadExitResidue_boundary_or_axisWallRun_or_lastWallRun_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (huPos : 0 < (rlc_dualReflect u) 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hresidue : RlcCentralFacePositiveBadExitResidue gamma gamma' rho u v) :
-- imply
  ((rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) ∨ RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u ∨ RlcCentralFacePositiveWallRunSurgeryAt gamma gamma' rho L u := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExitResidue_boundary_or_axisWallRun_or_lastWallRun L hfaith q huPos huv hbad hresidue

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_surgeryResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma twoSignedBadExits_PIMS_or_surgeryResidue_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hu'Pos : 0 < (rlc_dualReflect u') 0) :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨ RlcCentralFacePairedBadExitSurgeryResidue gamma gamma' rho L u u' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_surgeryResidue L hfaith hno q q' huv hbad hu'v' hbad' huNeg hu'Pos

/--
[rlc_negativeWallRun_lastEdge_reflectedRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negativeWallRun_lastEdge_reflectedRight_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hrun : RlcCentralFaceNegativeWallRunSurgeryAt gamma gamma' rho L u)
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (huNotLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1) :
-- imply
  ∃ t : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧ s(rlc_dualReflect t, rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_negativeWallRun_lastEdge_reflectedRight hrun huNeg huNotLeft

/--
[rlc_positiveWallRun_lastEdge_reflectedLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveWallRun_lastEdge_reflectedLeft_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hrun : RlcCentralFacePositiveWallRunSurgeryAt gamma gamma' rho L u)
  (huPos : 0 < (rlc_dualReflect u) 0)
  (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
-- imply
  ∃ t : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧ s(rlc_dualReflect t, rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_positiveWallRun_lastEdge_reflectedLeft hrun huPos huNotRight

/--
[rlc_positiveAxisAllWallRun_lastEdge_reflectedLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveAxisAllWallRun_lastEdge_reflectedLeft_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hrun : RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u)
  (huPos : 0 < (rlc_dualReflect u) 0)
  (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
-- imply
  ∃ t : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧ s(rlc_dualReflect t, rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_positiveAxisAllWallRun_lastEdge_reflectedLeft hrun huPos huNotRight

/--
[rlc_negativeWallRun_lastEdge_traceStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negativeWallRun_lastEdge_traceStep_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hrun : RlcCentralFaceNegativeWallRunSurgeryAt gamma gamma' rho L u)
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (huNotLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1) :
-- imply
  ∃ (t z w : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧ z ∈ rlc_pathVertices gamma.1 ∧ w ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect t = rlc_flipX z ∧ rlc_dualReflect u = rlc_flipX w ∧ s(z, w) ∈ rlc_pathEdges gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_negativeWallRun_lastEdge_traceStep hrun huNeg huNotLeft

/--
[rlc_positiveWallRun_lastEdge_traceStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveWallRun_lastEdge_traceStep_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hrun : RlcCentralFacePositiveWallRunSurgeryAt gamma gamma' rho L u)
  (huPos : 0 < (rlc_dualReflect u) 0)
  (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
-- imply
  ∃ (t z w : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧ z ∈ rlc_pathVertices gamma'.1 ∧ w ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect t = rlc_flipX z ∧ rlc_dualReflect u = rlc_flipX w ∧ s(z, w) ∈ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_positiveWallRun_lastEdge_traceStep hrun huPos huNotRight

/--
[rlc_positiveAxisAllWallRun_lastEdge_traceStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveAxisAllWallRun_lastEdge_traceStep_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hrun : RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u)
  (huPos : 0 < (rlc_dualReflect u) 0)
  (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
-- imply
  ∃ (t z w : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧ z ∈ rlc_pathVertices gamma'.1 ∧ w ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect t = rlc_flipX z ∧ rlc_dualReflect u = rlc_flipX w ∧ s(z, w) ∈ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_positiveAxisAllWallRun_lastEdge_traceStep hrun huPos huNotRight

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_nonnegativePath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveAxisAllWallRun_reachableRight_or_nonnegativePath_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u)
  (huPos : 0 < (rlc_dualReflect u) 0) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ ∃ (A : Site 2) (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A u), p.IsPath ∧ rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧ rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∧ (∀ e ∈ p.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧ (∀ z ∈ p.support, rlc_dualReflect z ∉ rlc_pathVertices gamma.1) ∧ ∀ z ∈ p.support, 0 ≤ (rlc_dualReflect z) 0 := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_nonnegativePath L hfaith hrun huPos

/--
[rlc_nonnegative_wallPath_edge_reflectedLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_nonnegative_wallPath_edge_reflectedLeft_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {A u : Site 2}
  {p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A u}
  {f g : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hpWall : ∀ e ∈ p.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hpNoRight : ∀ z ∈ p.support, rlc_dualReflect z ∉ rlc_pathVertices gamma.1)
  (hpNonneg : ∀ z ∈ p.support, 0 ≤ (rlc_dualReflect z) 0)
  (hfg : s(f, g) ∈ p.edges) :
-- imply
  s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_nonnegative_wallPath_edge_reflectedLeft hfaith p hpWall hpNoRight hpNonneg hfg

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_reflectedLeftPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveAxisAllWallRun_reachableRight_or_reflectedLeftPath_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u)
  (huPos : 0 < (rlc_dualReflect u) 0) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ ∃ (A : Site 2) (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A u), p.IsPath ∧ rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧ rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∧ (∀ z ∈ p.support, rlc_dualReflect z ∉ rlc_pathVertices gamma.1) ∧ ∀ {f g : Site 2}, s(f, g) ∈ p.edges → s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_reflectedLeftPath L hfaith hrun huPos

/--
[rlc_pathSuffix_closed_under_pathEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_pathSuffix_closed_under_pathEdge_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b z x y : V}
  {W : G.Walk a b}
-- given
  (hW : W.IsPath)
  (hz : z ∈ W.support)
  (hxSuffix : x ∈ (W.dropUntil z hz).support)
  (hxNe : x ≠ z)
  (hxy : s(x, y) ∈ W.edges) :
-- imply
  y ∈ (W.dropUntil z hz).support := by
-- proof
  apply StatMech.Universality.rlc_pathSuffix_closed_under_pathEdge W hW hz hxSuffix hxNe hxy

/--
[rlc_walk_end_mem_pathSuffix_of_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_walk_end_mem_pathSuffix_of_avoid_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b z x y : V}
  {W : G.Walk a b}
  {q : G.Walk x y}
-- given
  (hW : W.IsPath)
  (hz : z ∈ W.support)
  (hxSuffix : x ∈ (W.dropUntil z hz).support)
  (hqEdges : ∀ e ∈ q.edges, e ∈ W.edges)
  (hqAvoid : z ∉ q.support) :
-- imply
  y ∈ (W.dropUntil z hz).support := by
-- proof
  apply StatMech.Universality.rlc_walk_end_mem_pathSuffix_of_avoid W hW hz q hxSuffix hqEdges hqAvoid

/--
[rlc_walk_end_mem_pathSuffix_iff_of_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_walk_end_mem_pathSuffix_iff_of_avoid_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b z x y : V}
  {W : G.Walk a b}
  {q : G.Walk x y}
-- given
  (hW : W.IsPath)
  (hz : z ∈ W.support)
  (hqEdges : ∀ e ∈ q.edges, e ∈ W.edges)
  (hqAvoid : z ∉ q.support) :
-- imply
  x ∈ (W.dropUntil z hz).support ↔ y ∈ (W.dropUntil z hz).support := by
-- proof
  apply StatMech.Universality.rlc_walk_end_mem_pathSuffix_iff_of_avoid W hW hz q hqEdges hqAvoid

/--
[rlc_walk_all_positive_or_last_nonpositive_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_walk_all_positive_or_last_nonpositive_decomp_eq
  {G : SimpleGraph V}
  {f : V → Int}
  {x y : V}
  {w : G.Walk x y}
-- given
  (hy : 0 < f y) :
-- imply
  (∀ z ∈ w.support, 0 < f z) ∨ ∃ (a b : V) (p : G.Walk x a) (r : G.Walk b y) (hab : G.Adj a b), f a ≤ 0 ∧ 0 < f b ∧ (∀ z ∈ r.support, 0 < f z) ∧ w = p.append (.cons hab r) := by
-- proof
  apply StatMech.Universality.rlc_walk_all_positive_or_last_nonpositive_decomp f w hy

/--
[rlc_mem_ambientCrossingWalk_edges_of_mem_pathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_mem_ambientCrossingWalk_edges_of_mem_pathEdges_eq
  {a b c d : Int}
  {tau : RlcCrossingPath a b c d}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_pathEdges tau) :
-- imply
  e ∈ (rlc_ambientCrossingWalk tau).edges := by
-- proof
  apply StatMech.Universality.rlc_mem_ambientCrossingWalk_edges_of_mem_pathEdges tau he

/--
[rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges_eq
  {a b c d : Int}
  {tau : RlcCrossingPath a b c d}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_reflectedPathEdges tau) :
-- imply
  e ∈ ((rlc_ambientCrossingWalk tau).map rlc_flipXLatticeHom).edges := by
-- proof
  apply StatMech.Universality.rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges tau he

/--
[rlc_reflectedAmbientCrossingWalk_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedAmbientCrossingWalk_isPath_eq
  {a b c d : Int}
  {tau : RlcCrossingPath a b c d} :
-- imply
  ((rlc_ambientCrossingWalk tau).map rlc_flipXLatticeHom).IsPath := by
-- proof
  apply StatMech.Universality.rlc_reflectedAmbientCrossingWalk_isPath tau

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_firstIntersectionSuffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveAxisAllWallRun_reachableRight_or_firstIntersectionSuffix_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u)
  (huPos : 0 < (rlc_dualReflect u) 0) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ ∃ (z : Site 2) (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support) (A : Site 2) (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A u), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ p.IsPath ∧ (∀ x ∈ p.support, rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∧ rlc_dualReflect u ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hz).support := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_firstIntersectionSuffix L hfaith hrun huPos

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_axisSuffix_or_strictEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveWallRun_reachableRight_or_axisSuffix_or_strictEntry_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFacePositiveWallRunSurgeryAt gamma gamma' rho L u)
  (huPos : 0 < (rlc_dualReflect u) 0) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ RlcCentralFacePositiveReflectedLeftAxisSuffixAt gamma gamma' rho u ∨ RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_axisSuffix_or_strictEntry L hfaith hrun huPos

/--
[rlc_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {c u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk c u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hcEnd : rlc_dualReflect c = (gamma'.1.2.1 : Site 2))
  (hqNoRight : ∀ x ∈ q.support, rlc_dualReflect x ∉ rlc_pathVertices gamma.1)
  (hqReflectedLeft : ∀ {f g : Site 2}, s(f, g) ∈ q.edges → s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_reflectedPathEdges gamma'.1) :
-- imply
  ∃ (z : Site 2) (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect u ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hz).support := by
-- proof
  apply StatMech.Universality.rlc_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix hfaith q hcEnd hqNoRight hqReflectedLeft

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictEntry_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFacePositiveWallRunSurgeryAt gamma gamma' rho L u)
  (huPos : 0 < (rlc_dualReflect u) 0) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ (∃ (z : Site 2) (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect u ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hz).support) ∨ RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictEntry L hfaith hrun huPos

/--
[rlc_nonpositive_wallPath_edge_reflectedRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_nonpositive_wallPath_edge_reflectedRight_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {A u : Site 2}
  {p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A u}
  {f g : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hpWall : ∀ e ∈ p.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hpNoLeft : ∀ z ∈ p.support, rlc_dualReflect z ∉ rlc_pathVertices gamma'.1)
  (hpNonpos : ∀ z ∈ p.support, (rlc_dualReflect z) 0 ≤ 0)
  (hfg : s(f, g) ∈ p.edges) :
-- imply
  s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_reflectedPathEdges gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_nonpositive_wallPath_edge_reflectedRight hfaith p hpWall hpNoLeft hpNonpos hfg

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_axisSuffix_or_strictEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma negativeWallRun_reachableLeft_or_axisSuffix_or_strictEntry_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFaceNegativeWallRunSurgeryAt gamma gamma' rho L u)
  (huNeg : (rlc_dualReflect u) 0 < 0) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma'.1) ∨ RlcCentralFaceNegativeReflectedRightAxisSuffixAt gamma gamma' rho u ∨ RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_axisSuffix_or_strictEntry L hfaith hrun huNeg

/--
[rlc_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {c u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk c u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hcStart : rlc_dualReflect c = (gamma.1.1 : Site 2))
  (hqNoLeft : ∀ x ∈ q.support, rlc_dualReflect x ∉ rlc_pathVertices gamma'.1)
  (hqReflectedRight : ∀ {f g : Site 2}, s(f, g) ∈ q.edges → s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_reflectedPathEdges gamma.1) :
-- imply
  ∃ (z : Site 2) (hz : rlc_flipX z ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect u ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hz).support := by
-- proof
  apply StatMech.Universality.rlc_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix hfaith q hcStart hqNoLeft hqReflectedRight

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictEntry_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFaceNegativeWallRunSurgeryAt gamma gamma' rho L u)
  (huNeg : (rlc_dualReflect u) 0 < 0) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma'.1) ∨ (∃ (z : Site 2) (hz : rlc_flipX z ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect u ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hz).support) ∨ RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictEntry L hfaith hrun huNeg

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.boxBoundary_reachableContacts_or_strictReflectedBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma boxBoundary_reachableContacts_or_strictReflectedBarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace u)
  (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ (∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ 0 < (rlc_dualReflect z) 0 ∧ ∃ w ∈ rlc_pathVertices gamma'.1, rlc_dualReflect z = rlc_flipX w) ∨ ∃ z : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace z ∧ (rlc_dualReflect z) 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1, rlc_dualReflect z = rlc_flipX w := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.boxBoundary_reachableContacts_or_strictReflectedBarrier L hfaith hu huBoundary

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.boxBoundary_reachableContacts_or_strictResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma boxBoundary_reachableContacts_or_strictResidue_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hu : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace u)
  (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ RlcCentralFaceStrictReflectedBarrierResidue gamma gamma' rho L := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.boxBoundary_reachableContacts_or_strictResidue L hfaith hu huBoundary

/--
[rlc_positiveStrictWallEntry_firstIntersection_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveStrictWallEntry_firstIntersection_sameSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hentry : RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u) :
-- imply
  ∃ (z : Site 2) (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support) (b : Site 2), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect b ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support ∧ rlc_dualReflect u ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support ∧ (rlc_dualReflect b ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hz).support ↔ rlc_dualReflect u ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hz).support) := by
-- proof
  apply StatMech.Universality.rlc_positiveStrictWallEntry_firstIntersection_sameSide hfaith hentry

/--
[rlc_negativeStrictWallEntry_firstIntersection_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negativeStrictWallEntry_firstIntersection_sameSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hentry : RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u) :
-- imply
  ∃ (z : Site 2) (hz : rlc_flipX z ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support) (b : Site 2), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect b ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support ∧ rlc_dualReflect u ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support ∧ (rlc_dualReflect b ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hz).support ↔ rlc_dualReflect u ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hz).support) := by
-- proof
  apply StatMech.Universality.rlc_negativeStrictWallEntry_firstIntersection_sameSide hfaith hentry

/--
[rlc_positiveStrictWallEntry_regionFlank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveStrictWallEntry_regionFlank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hentry : RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u) :
-- imply
  ∃ (a b : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b ∧ s(rlc_dualReflect a, rlc_dualReflect b) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ rlc_dualReflect a ∈ rlc_connectorBox n ∧ rlc_dualReflect b ∈ rlc_connectorBox n ∧ ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma', h ∈ flankFaces (rlc_dualReflect a) (rlc_dualReflect b) := by
-- proof
  apply StatMech.Universality.rlc_positiveStrictWallEntry_regionFlank hentry

/--
[rlc_negativeStrictWallEntry_regionFlank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negativeStrictWallEntry_regionFlank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
-- given
  (hentry : RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u) :
-- imply
  ∃ (a b : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b ∧ s(rlc_dualReflect a, rlc_dualReflect b) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ rlc_dualReflect a ∈ rlc_connectorBox n ∧ rlc_dualReflect b ∈ rlc_connectorBox n ∧ ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma', h ∈ flankFaces (rlc_dualReflect a) (rlc_dualReflect b) := by
-- proof
  apply StatMech.Universality.rlc_negativeStrictWallEntry_regionFlank hentry

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExitResidue_left_boundary_or_wallRunDecomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma negativeBadExitResidue_left_boundary_or_wallRunDecomp_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hresidue : RlcCentralFaceNegativeBadExitResidue gamma gamma' rho u v) :
-- imply
  (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ ((rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) ∨ RlcCentralFaceNegativeWallRunDecompAt gamma gamma' rho L q := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.negativeBadExitResidue_left_boundary_or_wallRunDecomp L hfaith q huNeg huv hbad hresidue

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExitResidue_boundary_or_axisWallRun_or_wallRunDecomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveBadExitResidue_boundary_or_axisWallRun_or_wallRunDecomp_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (huPos : 0 < (rlc_dualReflect u) 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hresidue : RlcCentralFacePositiveBadExitResidue gamma gamma' rho u v) :
-- imply
  ((rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n) ∨ RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u ∨ RlcCentralFacePositiveWallRunDecompAt gamma gamma' rho L q := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExitResidue_boundary_or_axisWallRun_or_wallRunDecomp L hfaith q huPos huv hbad hresidue

/--
[RlcCentralFaceNegativeStrictWallEntryDecompAt.nonwallGoodContourEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma nonwallGoodContourEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
-- given
  (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ L.boundary.contour.edges ∧ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceNegativeStrictWallEntryDecompAt.nonwallGoodContourEdge hentry

/--
[rlc_goodComponentContacts_or_nonwallEdgeMissingContactIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_nonwallEdgeMissingContactIncidence_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {f g : Site 2}
-- given
  (hfgContour : s(f, g) ∈ B.contour.edges)
  (hcarrier : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g)
  (hnonwall : s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma') :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceNonwallGoodContourEdgeMissingContactIncidence B f g := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_nonwallEdgeMissingContactIncidence hfgContour hcarrier hnonwall

/--
[RlcCentralFaceNegativeStrictWallEntryDecompAt.anchoredNonwallGoodContourEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma anchoredNonwallGoodContourEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
-- given
  (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ L.boundary.contour.edges ∧ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace f ∧ (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace g := by
-- proof
  apply StatMech.Universality.RlcCentralFaceNegativeStrictWallEntryDecompAt.anchoredNonwallGoodContourEdge hentry

/--
[rlc_goodComponentContacts_or_anchoredNonwallEdgeMissingContactIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_or_anchoredNonwallEdgeMissingContactIncidence_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {f g : Site 2}
-- given
  (hfgContour : s(f, g) ∈ B.contour.edges)
  (hcarrier : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g)
  (hnonwall : s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hfirstF : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace f)
  (hfirstG : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable B.firstFace g) :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence B f g := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_or_anchoredNonwallEdgeMissingContactIncidence hfgContour hcarrier hnonwall hfirstF hfirstG

/--
[rlc_goodComponentContacts_of_retainedAnchorTraceIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_goodComponentContacts_of_retainedAnchorTraceIncidence_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
-- given
  (hinc : RlcCentralFaceRetainedAnchorTraceIncidence B) :
-- imply
  RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho := by
-- proof
  apply StatMech.Universality.rlc_goodComponentContacts_of_retainedAnchorTraceIncidence hinc

/--
[rlc_not_anchoredMissingIncidence_of_retainedAnchorTraceIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_not_anchoredMissingIncidence_of_retainedAnchorTraceIncidence_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
  {f g : Site 2}
-- given
  (hinc : RlcCentralFaceRetainedAnchorTraceIncidence B) :
-- imply
  ¬ RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence B f g := by
-- proof
  apply StatMech.Universality.rlc_not_anchoredMissingIncidence_of_retainedAnchorTraceIncidence hinc

/--
[rlc_centralFacePIMS_success_of_retainedAnchorTraceIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_success_of_retainedAnchorTraceIncidence_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
-- given
  (hinc : RlcCentralFaceRetainedAnchorTraceIncidence B) :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_success_of_retainedAnchorTraceIncidence gamma gamma' rho hinc

/--
[rlc_negativeStrictEntry_reachableLeft_or_prefixAvoidsOriginalContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negativeStrictEntry_reachableLeft_or_prefixAvoidsOriginalContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
-- given
  (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ RlcCentralFaceNegativeStrictEntryPrefixAvoidsOriginalContactAt gamma gamma' rho L q := by
-- proof
  apply StatMech.Universality.rlc_negativeStrictEntry_reachableLeft_or_prefixAvoidsOriginalContact hentry

/--
[rlc_positiveStrictEntry_reachableRight_or_prefixAvoidsOriginalContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveStrictEntry_reachableRight_or_prefixAvoidsOriginalContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u}
-- given
  (hentry : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.secondFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ RlcCentralFacePositiveStrictEntryPrefixAvoidsOriginalContactAt gamma gamma' rho L q := by
-- proof
  apply StatMech.Universality.rlc_positiveStrictEntry_reachableRight_or_prefixAvoidsOriginalContact hentry

/--
[rlc_centralFacePIMS_success_or_strictEntryPrefixAvoidance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_success_or_strictEntryPrefixAvoidance_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u u' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q)
  (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q') :
-- imply
  (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma') ∨ RlcCentralFaceNegativeStrictEntryPrefixAvoidsOriginalContactAt gamma gamma' rho L q ∨ RlcCentralFacePositiveStrictEntryPrefixAvoidsOriginalContactAt gamma gamma' rho L q' := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_success_or_strictEntryPrefixAvoidance hfaith hneg hpos

/--
[rlc_centralFacePIMS_success_of_no_strictEntryPrefixAvoidance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_success_of_no_strictEntryPrefixAvoidance_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u u' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q)
  (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q')
  (hnegAvoid : ¬ RlcCentralFaceNegativeStrictEntryPrefixAvoidsOriginalContactAt gamma gamma' rho L q)
  (hposAvoid : ¬ RlcCentralFacePositiveStrictEntryPrefixAvoidsOriginalContactAt gamma gamma' rho L q') :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_success_of_no_strictEntryPrefixAvoidance hfaith hneg hpos hnegAvoid hposAvoid

/--
[rlc_positiveStrictWallEntry_of_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveStrictWallEntry_of_decomp_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u}
-- given
  (h : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u := by
-- proof
  apply StatMech.Universality.rlc_positiveStrictWallEntry_of_decomp h

/--
[rlc_negativeStrictWallEntry_of_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negativeStrictWallEntry_of_decomp_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
-- given
  (h : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u := by
-- proof
  apply StatMech.Universality.rlc_negativeStrictWallEntry_of_decomp h

/--
[rlc_site_eta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_site_eta_eq
  {x : Site 2} :
-- imply
  (![x 0, x 1] : Site 2) = x := by
-- proof
  apply StatMech.Universality.rlc_site_eta x

/--
[rlc_site_mk_eq_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_site_mk_eq_site_eq
  {a b : Int}
  {x : Site 2} :
-- imply
  ((![a, b] : Site 2) = x ↔ a = x 0 ∧ b = x 1) := by
-- proof
  apply StatMech.Universality.rlc_site_mk_eq_site a b x

/--
[rlc_int_self_ne_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_int_self_ne_add_one_eq
  {a : Int} :
-- imply
  a ≠ a + 1 := by
-- proof
  apply StatMech.Universality.rlc_int_self_ne_add_one a

/--
[rlc_int_self_ne_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_int_self_ne_sub_one_eq
  {a : Int} :
-- imply
  a ≠ a - 1 := by
-- proof
  apply StatMech.Universality.rlc_int_self_ne_sub_one a

/--
[rlc_int_add_one_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_int_add_one_ne_self_eq
  {a : Int} :
-- imply
  a + 1 ≠ a := by
-- proof
  apply StatMech.Universality.rlc_int_add_one_ne_self a

/--
[rlc_int_sub_one_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_int_sub_one_ne_self_eq
  {a : Int} :
-- imply
  a - 1 ≠ a := by
-- proof
  apply StatMech.Universality.rlc_int_sub_one_ne_self a

/--
[rlc_int_add_two_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_int_add_two_ne_self_eq
  {a : Int} :
-- imply
  a + 1 + 1 ≠ a := by
-- proof
  apply StatMech.Universality.rlc_int_add_two_ne_self a

/--
[rlc_int_sub_two_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_int_sub_two_ne_self_eq
  {a : Int} :
-- imply
  a - 1 - 1 ≠ a := by
-- proof
  apply StatMech.Universality.rlc_int_sub_two_ne_self a

/--
[rlc_int_self_ne_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_int_self_ne_add_two_eq
  {a : Int} :
-- imply
  a ≠ a + 1 + 1 := by
-- proof
  apply StatMech.Universality.rlc_int_self_ne_add_two a

/--
[rlc_int_self_ne_sub_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_int_self_ne_sub_two_eq
  {a : Int} :
-- imply
  a ≠ a - 1 - 1 := by
-- proof
  apply StatMech.Universality.rlc_int_self_ne_sub_two a

/--
[rlc_int_sub_one_ne_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_int_sub_one_ne_add_one_eq
  {a : Int} :
-- imply
  a - 1 ≠ a + 1 := by
-- proof
  apply StatMech.Universality.rlc_int_sub_one_ne_add_one a

/--
[rlc_int_add_one_ne_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_int_add_one_ne_sub_one_eq
  {a : Int} :
-- imply
  a + 1 ≠ a - 1 := by
-- proof
  apply StatMech.Universality.rlc_int_add_one_ne_sub_one a

/--
[rlc_flankFaces_step_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_flankFaces_step_right_eq
  {x : Site 2} :
-- imply
  flankFaces x ![x 0 + 1, x 1] = s((![x 0, x 1 - 1] : Site 2), x) := by
-- proof
  apply StatMech.Universality.rlc_flankFaces_step_right x

/--
[rlc_flankFaces_step_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_flankFaces_step_left_eq
  {x : Site 2} :
-- imply
  flankFaces x ![x 0 - 1, x 1] = s((![x 0 - 1, x 1 - 1] : Site 2), ![x 0 - 1, x 1]) := by
-- proof
  apply StatMech.Universality.rlc_flankFaces_step_left x

/--
[rlc_flankFaces_step_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_flankFaces_step_top_eq
  {x : Site 2} :
-- imply
  flankFaces x ![x 0, x 1 + 1] = s((![x 0 - 1, x 1] : Site 2), x) := by
-- proof
  apply StatMech.Universality.rlc_flankFaces_step_top x

/--
[rlc_flankFaces_step_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_flankFaces_step_bottom_eq
  {x : Site 2} :
-- imply
  flankFaces x ![x 0, x 1 - 1] = s((![x 0 - 1, x 1 - 1] : Site 2), ![x 0, x 1 - 1]) := by
-- proof
  apply StatMech.Universality.rlc_flankFaces_step_bottom x

/--
[rlc_isPath_incident_edge_eq_of_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_isPath_incident_edge_eq_of_two_eq
  {G : SimpleGraph V}
  {start finish x y z w : V}
  {p : G.Walk start finish}
-- given
  (hp : p.IsPath)
  (hxy : s(x, y) ∈ p.edges)
  (hyz : s(y, z) ∈ p.edges)
  (hxz : x ≠ z)
  (hyw : s(y, w) ∈ p.edges) :
-- imply
  w = x ∨ w = z := by
-- proof
  apply StatMech.Universality.rlc_isPath_incident_edge_eq_of_two p hp hxy hyz hxz hyw

/--
[rlc_isPath_exists_other_incident_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_isPath_exists_other_incident_edge_eq
  {G : SimpleGraph V}
  {start finish b c : V}
  {p : G.Walk start finish}
-- given
  (hp : p.IsPath)
  (hbc : s(b, c) ∈ p.edges)
  (hbStart : b ≠ start)
  (hbFinish : b ≠ finish) :
-- imply
  ∃ d : V, s(b, d) ∈ p.edges ∧ d ≠ c := by
-- proof
  apply StatMech.Universality.rlc_isPath_exists_other_incident_edge p hp hbc hbStart hbFinish

/--
[rlc_positive_reflectedLeft_third_incident_nonwall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positive_reflectedLeft_third_incident_nonwall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y z w : Site 2}
-- given
  (hyPos : 0 < y 0)
  (hyNoRight : y ∉ rlc_pathVertices gamma.1)
  (hxy : s(x, y) ∈ rlc_reflectedPathEdges gamma'.1)
  (hyz : s(y, z) ∈ rlc_reflectedPathEdges gamma'.1)
  (hxz : x ≠ z)
  (hywNeX : s(y, w) ≠ s(x, y))
  (hywNeZ : s(y, w) ≠ s(y, z)) :
-- imply
  s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_positive_reflectedLeft_third_incident_nonwall gamma gamma' hyPos hyNoRight hxy hyz hxz hywNeX hywNeZ

/--
[rlc_negative_reflectedRight_third_incident_nonwall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negative_reflectedRight_third_incident_nonwall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y z w : Site 2}
-- given
  (hyNeg : y 0 < 0)
  (hyNoLeft : y ∉ rlc_pathVertices gamma'.1)
  (hxy : s(x, y) ∈ rlc_reflectedPathEdges gamma.1)
  (hyz : s(y, z) ∈ rlc_reflectedPathEdges gamma.1)
  (hxz : x ≠ z)
  (hywNeX : s(y, w) ≠ s(x, y))
  (hywNeZ : s(y, w) ≠ s(y, z)) :
-- imply
  s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_negative_reflectedRight_third_incident_nonwall gamma gamma' hyNeg hyNoLeft hxy hyz hxz hywNeX hywNeZ

/--
[rlc_centralFaceRegion_continue_consecutive_wall_flank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFaceRegion_continue_consecutive_wall_flank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {x y z h : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y)
  (hyz : (hypercubicLattice 2).Adj y z)
  (hxz : x ≠ z)
  (hyInterior : -2 * n < y 0 ∧ y 0 < 2 * n ∧ -n < y 1 ∧ y 1 < n)
  (hother : ∀ w : Site 2, (hypercubicLattice 2).Adj y w → s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) → s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces x y) :
-- imply
  ∃ k ∈ flankFaces y z, k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFaceRegion_continue_consecutive_wall_flank gamma gamma' hxy hyz hxz hyInterior hother hhRegion hh

/--
[rlc_walk_terminal_regionFlank_of_consecutive_detours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_walk_terminal_regionFlank_of_consecutive_detours_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {b u : Site 2}
  {q : (hypercubicLattice 2).Walk b u}
  {h : Site 2}
-- given
  (hqNotNil : ¬ q.Nil)
  (hqInterior : ∀ y ∈ q.support, -2 * n < y 0 ∧ y 0 < 2 * n ∧ -n < y 1 ∧ y 1 < n)
  (hthird : ∀ {x y z w : Site 2}, s(x, y) ∈ q.edges → s(y, z) ∈ q.edges → x ≠ z → (hypercubicLattice 2).Adj y w → s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) → s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces b q.snd) :
-- imply
  ∃ k ∈ flankFaces q.penultimate u, k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_walk_terminal_regionFlank_of_consecutive_detours gamma gamma' q hqNotNil hqInterior hthird hhRegion hh

/--
[rlc_positive_reflectedLeft_walk_terminal_regionFlank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positive_reflectedLeft_walk_terminal_regionFlank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {b u : Site 2}
  {r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u}
  {h : Site 2}
-- given
  (hrPos : ∀ x ∈ r.support, 0 < (rlc_dualReflect x) 0)
  (hrNoRight : ∀ x ∈ r.support, rlc_dualReflect x ∉ rlc_pathVertices gamma.1)
  (hrLeft : ∀ {f g : Site 2}, s(f, g) ∈ r.edges → s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_reflectedPathEdges gamma'.1)
  (hrNotNil : ¬ r.Nil)
  (hrInterior : ∀ x ∈ r.support, -2 * n < (rlc_dualReflect x) 0 ∧ (rlc_dualReflect x) 0 < 2 * n ∧ -n < (rlc_dualReflect x) 1 ∧ (rlc_dualReflect x) 1 < n)
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect b) (rlc_dualReflect r.snd)) :
-- imply
  ∃ k ∈ flankFaces (rlc_dualReflect r.penultimate) (rlc_dualReflect u), k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_positive_reflectedLeft_walk_terminal_regionFlank r hrPos hrNoRight hrLeft hrNotNil hrInterior hhRegion hh

/--
[rlc_negative_reflectedRight_walk_terminal_regionFlank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negative_reflectedRight_walk_terminal_regionFlank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {b u : Site 2}
  {r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u}
  {h : Site 2}
-- given
  (hrNeg : ∀ x ∈ r.support, (rlc_dualReflect x) 0 < 0)
  (hrNoLeft : ∀ x ∈ r.support, rlc_dualReflect x ∉ rlc_pathVertices gamma'.1)
  (hrRight : ∀ {f g : Site 2}, s(f, g) ∈ r.edges → s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_reflectedPathEdges gamma.1)
  (hrNotNil : ¬ r.Nil)
  (hrInterior : ∀ x ∈ r.support, -2 * n < (rlc_dualReflect x) 0 ∧ (rlc_dualReflect x) 0 < 2 * n ∧ -n < (rlc_dualReflect x) 1 ∧ (rlc_dualReflect x) 1 < n)
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect b) (rlc_dualReflect r.snd)) :
-- imply
  ∃ k ∈ flankFaces (rlc_dualReflect r.penultimate) (rlc_dualReflect u), k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_negative_reflectedRight_walk_terminal_regionFlank r hrNeg hrNoLeft hrRight hrNotNil hrInterior hhRegion hh

/--
[rlc_centralFaceRegion_first_wall_flank_of_nonwall_entry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFaceRegion_first_wall_flank_of_nonwall_entry_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {a b c d h : Site 2}
-- given
  (hba : (hypercubicLattice 2).Adj b a)
  (hbc : (hypercubicLattice 2).Adj b c)
  (hbd : (hypercubicLattice 2).Adj b d)
  (hac : a ≠ c)
  (hdc : d ≠ c)
  (hentryNot : s(a, b) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hbdWall : s(b, d) ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hbInterior : -2 * n < b 0 ∧ b 0 < 2 * n ∧ -n < b 1 ∧ b 1 < n)
  (hother : ∀ w : Site 2, (hypercubicLattice 2).Adj b w → s(b, w) ≠ s(d, b) → s(b, w) ≠ s(b, c) → s(b, w) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces a b) :
-- imply
  ∃ k ∈ flankFaces b c, k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFaceRegion_first_wall_flank_of_nonwall_entry gamma gamma' hba hbc hbd hac hdc hentryNot hbdWall hbInterior hother hhRegion hh

/--
[rlc_positiveStrictWallEntryDecomp_boundary_or_terminalRegionFlank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveStrictWallEntryDecomp_boundary_or_terminalRegionFlank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hentry : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ ((rlc_dualReflect x) 0 = -2 * n ∨ (rlc_dualReflect x) 0 = 2 * n ∨ (rlc_dualReflect x) 1 = -n ∨ (rlc_dualReflect x) 1 = n)) ∨ ∃ (t h : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧ s(rlc_dualReflect t, rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma'.1 ∧ h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) := by
-- proof
  apply StatMech.Universality.rlc_positiveStrictWallEntryDecomp_boundary_or_terminalRegionFlank hfaith hentry

/--
[rlc_negativeStrictWallEntryDecomp_boundary_or_terminalRegionFlank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negativeStrictWallEntryDecomp_boundary_or_terminalRegionFlank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ ((rlc_dualReflect x) 0 = -2 * n ∨ (rlc_dualReflect x) 0 = 2 * n ∨ (rlc_dualReflect x) 1 = -n ∨ (rlc_dualReflect x) 1 = n)) ∨ ∃ (t h : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧ s(rlc_dualReflect t, rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma.1 ∧ h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) := by
-- proof
  apply StatMech.Universality.rlc_negativeStrictWallEntryDecomp_boundary_or_terminalRegionFlank hfaith hentry

/--
[rlc_positiveStrictWallEntryDecomp_boundary_or_terminalSideChange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_positiveStrictWallEntryDecomp_boundary_or_terminalSideChange_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hentry : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ ((rlc_dualReflect x) 0 = -2 * n ∨ (rlc_dualReflect x) 0 = 2 * n ∨ (rlc_dualReflect x) 1 = -n ∨ (rlc_dualReflect x) 1 = n)) ∨ ∃ (t h : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧ s(rlc_dualReflect t, rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma'.1 ∧ h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) ∧ s(rlc_dualReflect u, rlc_dualReflect v) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ rlc_dualReflect u ∈ rlc_connectorBox n ∧ rlc_dualReflect v ∈ rlc_connectorBox n ∧ ∀ k ∈ rlc_connectorCentralFaceRegion gamma gamma', k ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
-- proof
  apply StatMech.Universality.rlc_positiveStrictWallEntryDecomp_boundary_or_terminalSideChange hfaith hentry huv hbad

/--
[rlc_negativeStrictWallEntryDecomp_boundary_or_terminalSideChange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_negativeStrictWallEntryDecomp_boundary_or_terminalSideChange_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ ((rlc_dualReflect x) 0 = -2 * n ∨ (rlc_dualReflect x) 0 = 2 * n ∨ (rlc_dualReflect x) 1 = -n ∨ (rlc_dualReflect x) 1 = n)) ∨ ∃ (t h : Site 2), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧ s(rlc_dualReflect t, rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma.1 ∧ h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) ∧ s(rlc_dualReflect u, rlc_dualReflect v) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ rlc_dualReflect u ∈ rlc_connectorBox n ∧ rlc_dualReflect v ∈ rlc_connectorBox n ∧ ∀ k ∈ rlc_connectorCentralFaceRegion gamma gamma', k ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
-- proof
  apply StatMech.Universality.rlc_negativeStrictWallEntryDecomp_boundary_or_terminalSideChange hfaith hentry huv hbad

/--
[rlc_retainedAnchorTraceIncidence_of_strictEntryOriginalContactSurgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_retainedAnchorTraceIncidence_of_strictEntryOriginalContactSurgery_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u u' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hsurgery : RlcCentralFaceStrictEntryOriginalContactSurgery gamma gamma' rho L)
  (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q)
  (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q') :
-- imply
  RlcCentralFaceRetainedAnchorTraceIncidence L.boundary := by
-- proof
  apply StatMech.Universality.rlc_retainedAnchorTraceIncidence_of_strictEntryOriginalContactSurgery hfaith hsurgery hneg hpos

/--
[rlc_centralFacePIMS_success_of_strictEntryOriginalContactSurgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_centralFacePIMS_success_of_strictEntryOriginalContactSurgery_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u u' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hsurgery : RlcCentralFaceStrictEntryOriginalContactSurgery gamma gamma' rho L)
  (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q)
  (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q') :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈ rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFacePIMS_success_of_strictEntryOriginalContactSurgery hfaith hsurgery hneg hpos

/--
[RlcCentralFacePairedTerminalSideChange.positiveIncoming_firstIntersectionCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveIncoming_firstIntersectionCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v u' v' : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hpaired : RlcCentralFacePairedTerminalSideChange gamma gamma' rho L u v u' v') :
-- imply
  ∃ (t' h' k' : Site 2) (c : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)), (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t' u' ∧ s(rlc_dualReflect t', rlc_dualReflect u') ∈ rlc_reflectedPathEdges gamma'.1 ∧ h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧ c.IsCycle ∧ (∀ e ∈ c.edges, e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧ phb_doubleDualEquiv.symm h' ∈ jec_leftRegion c ∧ s(rlc_dualReflect t', rlc_dualReflect u') ∈ c.edges ∧ phb_doubleDualEquiv.symm k' ∉ jec_leftRegion c := by
-- proof
  apply StatMech.Universality.RlcCentralFacePairedTerminalSideChange.positiveIncoming_firstIntersectionCycle hfaith hpaired

/--
[RlcCentralFacePairedTerminalSideChange.nonwallGoodContourEdge_or_sameWindingSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma nonwallGoodContourEdge_or_sameWindingSides_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v u' v' : Site 2}
-- given
  (hpaired : RlcCentralFacePairedTerminalSideChange gamma gamma' rho L u v u' v') :
-- imply
  (∃ f g : Site 2, s(f, g) ∈ L.boundary.contour.edges ∧ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma') ∨ ∃ t h t' h' k k' : Site 2, h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧ flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧ (let C := (L.boundary.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom (phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ↔ phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧ (phb_doubleDualEquiv.symm k ∈ jec_leftRegion C ↔ phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C)) := by
-- proof
  apply StatMech.Universality.RlcCentralFacePairedTerminalSideChange.nonwallGoodContourEdge_or_sameWindingSides hpaired

/--
[rlc_pairedStrictWallEntryDecomp_boundary_or_terminalSideChange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_pairedStrictWallEntryDecomp_boundary_or_terminalSideChange_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q)
  (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v') :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ ((rlc_dualReflect x) 0 = -2 * n ∨ (rlc_dualReflect x) 0 = 2 * n ∨ (rlc_dualReflect x) 1 = -n ∨ (rlc_dualReflect x) 1 = n)) ∨ RlcCentralFacePairedTerminalSideChange gamma gamma' rho L u v u' v' := by
-- proof
  apply StatMech.Universality.rlc_pairedStrictWallEntryDecomp_boundary_or_terminalSideChange hfaith hneg hpos huv hbad hu'v' hbad'

/--
[rlc_pairedStrictWallEntryDecomp_boundary_or_nonwall_or_orderedSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_pairedStrictWallEntryDecomp_boundary_or_nonwall_or_orderedSides_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q)
  (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v') :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ ((rlc_dualReflect x) 0 = -2 * n ∨ (rlc_dualReflect x) 0 = 2 * n ∨ (rlc_dualReflect x) 1 = -n ∨ (rlc_dualReflect x) 1 = n)) ∨ (∃ f g : Site 2, s(f, g) ∈ L.boundary.contour.edges ∧ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma') ∨ ((∃ t h t' h' k k' : Site 2, h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧ flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧ (let C := (L.boundary.contour.mapLe (faceBoundaryGraph_le (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map rlc_dualReflectLatticeHom (phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ↔ phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧ (phb_doubleDualEquiv.symm k ∈ jec_leftRegion C ↔ phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C))) ∧ RlcCentralFacePairedFirstIntersectionSideData gamma gamma' u u') := by
-- proof
  apply StatMech.Universality.rlc_pairedStrictWallEntryDecomp_boundary_or_nonwall_or_orderedSides hfaith hneg hpos huv hbad hu'v' hbad'

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_boundary_or_pairedTerminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma twoBadMiddle_extreme_and_boundary_or_pairedTerminal_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {r : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v L.boundary.secondFace}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
  {t : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v}
-- given
  (haExact : ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
  (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
  (hdecomp : a = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons huv r))
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
  (hdecomp' : r.reverse = (q'.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons hu'v' t))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hu'Pos : 0 < (rlc_dualReflect u') 0)
  (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q)
  (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q') :
-- imply
  (∃ (f g : Site 2) (k : Int), s(f, g) ∈ L.boundary.contour.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]) ∧ (k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k)) ∧ ((∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ ((rlc_dualReflect x) 0 = -2 * n ∨ (rlc_dualReflect x) 0 = 2 * n ∨ (rlc_dualReflect x) 1 = -n ∨ (rlc_dualReflect x) 1 = n)) ∨ RlcCentralFacePairedTerminalSideChange gamma gamma' rho L u v u' v') := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_boundary_or_pairedTerminal L haExact haAvoid hfaith q r huv hbad hdecomp q' t hu'v' hbad' hdecomp' huNeg hu'Pos hneg hpos

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_nonwallGoodContourEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma twoBadMiddle_extreme_and_nonwallGoodContourEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {r : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v L.boundary.secondFace}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
  {t : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v}
-- given
  (haExact : ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
  (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hdecomp : a = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons huv r))
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hdecomp' : r.reverse = (q'.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons hu'v' t))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hu'Pos : 0 < (rlc_dualReflect u') 0)
  (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  (∃ (f g : Site 2) (k : Int), s(f, g) ∈ L.boundary.contour.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]) ∧ (k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k)) ∧ ∃ f g : Site 2, s(f, g) ∈ L.boundary.contour.edges ∧ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_nonwallGoodContourEdge L haExact haAvoid q r huv hdecomp q' t hu'v' hdecomp' huNeg hu'Pos hneg

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_goodComponentContacts_or_missingIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma twoBadMiddle_extreme_and_goodComponentContacts_or_missingIncidence_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {r : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v L.boundary.secondFace}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
  {t : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v}
-- given
  (haExact : ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
  (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hdecomp : a = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons huv r))
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hdecomp' : r.reverse = (q'.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons hu'v' t))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hu'Pos : 0 < (rlc_dualReflect u') 0)
  (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  (∃ (f g : Site 2) (k : Int), s(f, g) ∈ L.boundary.contour.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]) ∧ (k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k)) ∧ (RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ ∃ f g : Site 2, RlcCentralFaceNonwallGoodContourEdgeMissingContactIncidence L.boundary f g) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_goodComponentContacts_or_missingIncidence L haExact haAvoid q r huv hdecomp q' t hu'v' hdecomp' huNeg hu'Pos hneg

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_goodComponentContacts_or_anchoredMissingIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma twoBadMiddle_extreme_and_goodComponentContacts_or_anchoredMissingIncidence_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {a : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk L.boundary.firstFace L.boundary.secondFace}
  {u v u' v' : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
  {r : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v L.boundary.secondFace}
  {q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u'}
  {t : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v}
-- given
  (haExact : ∀ e : Sym2 (Site 2), e ∈ L.boundary.contour.edges ↔ e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
  (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hdecomp : a = (q.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons huv r))
  (hu'v' : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
  (hdecomp' : r.reverse = (q'.mapLe (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append (.cons hu'v' t))
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (hu'Pos : 0 < (rlc_dualReflect u') 0)
  (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q) :
-- imply
  (∃ (f g : Site 2) (k : Int), s(f, g) ∈ L.boundary.contour.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) = s((![-1, k] : Site 2), ![0, k]) ∧ (k ≤ (gamma.1.1 : Site 2) 1 ∨ L.boundary.height + 1 < k)) ∧ (RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨ ∃ f g : Site 2, RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence L.boundary f g) := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_goodComponentContacts_or_anchoredMissingIncidence L haExact haAvoid q r huv hdecomp q' t hu'v' hdecomp' huNeg hu'Pos hneg

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRunDecomp_reachableRight_or_axisSuffix_or_strictEntryDecomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveWallRunDecomp_reachableRight_or_axisSuffix_or_strictEntryDecomp_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.secondFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFacePositiveWallRunDecompAt gamma gamma' rho L q)
  (huPos : 0 < (rlc_dualReflect u) 0) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ RlcCentralFacePositiveReflectedLeftAxisSuffixAt gamma gamma' rho u ∨ RlcCentralFacePositiveStrictWallEntryDecompAt gamma gamma' rho L q := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRunDecomp_reachableRight_or_axisSuffix_or_strictEntryDecomp L hfaith hrun huPos

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRunDecomp_reachableLeft_or_axisSuffix_or_strictEntryDecomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma negativeWallRunDecomp_reachableLeft_or_axisSuffix_or_strictEntryDecomp_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u : Site 2}
  {q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk L.boundary.firstFace u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFaceNegativeWallRunDecompAt gamma gamma' rho L q)
  (huNeg : (rlc_dualReflect u) 0 < 0) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma'.1) ∨ RlcCentralFaceNegativeReflectedRightAxisSuffixAt gamma gamma' rho u ∨ RlcCentralFaceNegativeStrictWallEntryDecompAt gamma gamma' rho L q := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRunDecomp_reachableLeft_or_axisSuffix_or_strictEntryDecomp L hfaith hrun huNeg

/--
[rlc_strictSurgeryResidue_of_strictCarrierSurgeryResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma rlc_strictSurgeryResidue_of_strictCarrierSurgeryResidue_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v u' v' : Site 2}
-- given
  (h : RlcCentralFaceStrictCarrierSurgeryResidue gamma gamma' rho L u v u' v') :
-- imply
  RlcCentralFaceStrictSurgeryResidue gamma gamma' rho L u u' := by
-- proof
  apply StatMech.Universality.rlc_strictSurgeryResidue_of_strictCarrierSurgeryResidue h

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictCarrierSurgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictCarrierSurgery_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFacePositiveWallRunSurgeryAt gamma gamma' rho L u)
  (huPos : 0 < (rlc_dualReflect u) 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  (∃ x : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace x ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨ (∃ (z : Site 2) (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect u ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hz).support) ∨ RlcCentralFacePositiveStrictCarrierSurgeryAt gamma gamma' rho L u v := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictCarrierSurgery L hfaith hrun huPos huv hbad

/--
[RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictCarrierSurgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean)
-/
@[path]
private lemma negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictCarrierSurgery_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
  {u v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrun : RlcCentralFaceNegativeWallRunSurgeryAt gamma gamma' rho L u)
  (huNeg : (rlc_dualReflect u) 0 < 0)
  (huv : (faceBoundaryGraph (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
  (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v) :
-- imply
  (∃ y : Site 2, (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable L.boundary.firstFace y ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨ (∃ (z : Site 2) (hz : rlc_flipX z ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect u ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hz).support) ∨ RlcCentralFaceNegativeStrictCarrierSurgeryAt gamma gamma' rho L u v := by
-- proof
  apply StatMech.Universality.RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictCarrierSurgery L hfaith hrun huNeg huv hbad


-- created on 2026-10-23
