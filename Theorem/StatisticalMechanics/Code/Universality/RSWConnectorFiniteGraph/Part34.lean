/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part47
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorOuter_numClusters_eq_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClustersBC (rlc_connectorOuterDualGraph gamma gamma') ⊥
        (rlc_connectorOuterDualConfig gamma gamma' tau) =
      Nat.card (BeffaraDC.pfdClosedDual
        (rlc_connectorAugmentedPlanarDomain gamma gamma')
        (FK.openSub (rlc_connectorAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma' tau))).ConnectedComponent := by
  rw [FK.numClustersBC, sup_bot_eq]
  change Nat.card
      (rlc_connectorOuterOpenGraph gamma gamma' tau).ConnectedComponent = _
  exact Nat.card_congr
    (rlc_connectorOuterComponentEquiv gamma gamma' tau)

theorem rlc_connectorOuterRandom_spoke_disjoint {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset
      (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset := by
  rw [Finset.disjoint_left]
  intro e hrandom hspoke
  rw [rlc_connectorOuterRandom_edgeFinset] at hrandom
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hrandom
  apply rlc_connectorOuterDualEdge_not_mem_spoke gamma gamma' f
  exact SimpleGraph.mem_edgeFinset.mp hspoke


theorem rlc_openCount_complement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) :
    FK.openCount G (fun e => !(omega e)) =
      G.edgeFinset.card - FK.openCount G omega := by
  have hclosed : FK.openCount G (fun e => !(omega e)) =
      FK.closedCount G omega := by
    unfold FK.openCount FK.closedCount
    congr 1
    ext e
    simp only [Finset.mem_filter]
    cases omega e <;> simp
  rw [hclosed]
  have hsum := FK.openCount_add_closedCount G omega
  omega


theorem rlc_connector_pfdDualEdgeFactor_eq_randomProduct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p : Real) :
    BeffaraDC.edgeProductCount p
        (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card
        ((rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card -
          (FK.openSub
            (rlc_connectorAugmentedPlanarDomain gamma gamma').G
            (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet.ncard) =
      ∏ f : Ising.kwg_Edge
          (rlc_connectorAugmentedPlanarDomain gamma gamma'),
        if !(rlc_connectorForceTraceConfig gamma gamma' tau f.1)
          then p else 1 - p := by
  let P := rlc_connectorAugmentedPlanarDomain gamma gamma'
  let forced := rlc_connectorForceTraceConfig gamma gamma' tau
  calc
    BeffaraDC.edgeProductCount p P.G.edgeFinset.card
        (P.G.edgeFinset.card - (FK.openSub P.G forced).edgeSet.ncard) =
      BeffaraDC.edgeProductCount p P.G.edgeFinset.card
        (FK.openCount P.G (fun e => !(forced e))) := by
          rw [rlc_openCount_complement,
            BeffaraDC.pfd_openSub_edge_ncard]
    _ = FK.edgeProduct P.G p (fun e => !(forced e)) :=
      (BeffaraDC.dlt_edgeProduct_eq_count P.G p
        (fun e => !(forced e))).symm
    _ = ∏ f : Ising.kwg_Edge P,
        if !(forced f.1) then p else 1 - p := by
      unfold FK.edgeProduct
      rw [← Finset.prod_attach P.G.edgeFinset, Finset.attach_eq_univ]
      let edgeEquiv : P.G.edgeFinset ≃ Ising.kwg_Edge P :=
        { toFun := fun e => ⟨e.1, by
            simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
          invFun := fun e => ⟨e.1, by
            simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
          left_inv := by intro e; rfl
          right_inv := by intro e; rfl }
      apply Fintype.prod_equiv edgeEquiv
      intro f
      simp only [edgeEquiv]
      rfl


theorem rlc_connectorOuter_randomEdgeProduct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p : Real) :
    (∏ e ∈ (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset,
        if rlc_connectorOuterDualConfig gamma gamma' tau e
          then p else 1 - p) =
      ∏ f : Ising.kwg_Edge
          (rlc_connectorAugmentedPlanarDomain gamma gamma'),
        if !(rlc_connectorForceTraceConfig gamma gamma' tau f.1)
          then p else 1 - p := by
  rw [rlc_connectorOuterRandom_edgeFinset,
    Finset.prod_image
      (fun a _ b _ h => rlc_connectorOuterDualEdge_injective gamma gamma' h)]
  apply Finset.prod_congr rfl
  intro f _
  rw [rlc_connectorOuterDualConfig_randomEdge]


theorem rlc_connectorOuter_spokeEdgeProduct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p : Real) :
    (∏ e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset,
        if rlc_connectorOuterDualConfig gamma gamma' tau e
          then p else 1 - p) =
      p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card := by
  calc
    (∏ e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset,
        if rlc_connectorOuterDualConfig gamma gamma' tau e
          then p else 1 - p) =
      ∏ _e ∈ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset, p := by
        apply Finset.prod_congr rfl
        intro e he
        rw [rlc_connectorOuterDualConfig_spoke gamma gamma' tau
          (SimpleGraph.mem_edgeFinset.mp he)]
        rfl
    _ = p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card := by
      simp


theorem rlc_connectorOuter_edgeProduct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p : Real) :
    FK.edgeProduct (rlc_connectorOuterDualGraph gamma gamma') p
        (rlc_connectorOuterDualConfig gamma gamma' tau) =
      p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card *
        BeffaraDC.edgeProductCount p
          (rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card
          ((rlc_connectorAugmentedPlanarDomain gamma gamma').G.edgeFinset.card -
            (FK.openSub
              (rlc_connectorAugmentedPlanarDomain gamma gamma').G
              (rlc_connectorForceTraceConfig gamma gamma' tau)).edgeSet.ncard) := by
  have hEdges : (rlc_connectorOuterDualGraph gamma gamma').edgeFinset =
      (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset ∪
        (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset := by
    ext e
    simp [rlc_connectorOuterDualGraph, SimpleGraph.mem_edgeFinset]
  unfold FK.edgeProduct
  rw [hEdges,
    Finset.prod_union (rlc_connectorOuterRandom_spoke_disjoint gamma gamma'),
    rlc_connectorOuter_randomEdgeProduct,
    ← rlc_connector_pfdDualEdgeFactor_eq_randomProduct,
    rlc_connectorOuter_spokeEdgeProduct]
  ring


theorem rlc_connectorOuter_bcWeight_eq_pfdDualWeight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) (p q : Real) :
    FK.bcWeight (rlc_connectorOuterDualGraph gamma gamma') ⊥ p q
        (rlc_connectorOuterDualConfig gamma gamma' tau) =
      p ^ (rlc_connectorOuterSpokeGraph gamma gamma').edgeFinset.card *
        BeffaraDC.pfdDualWeight
          (rlc_connectorAugmentedPlanarDomain gamma gamma') p q
          (FK.openSub
            (rlc_connectorAugmentedPlanarDomain gamma gamma').G
            (rlc_connectorForceTraceConfig gamma gamma' tau)) := by
  unfold FK.bcWeight BeffaraDC.pfdDualWeight
  rw [rlc_connectorOuter_edgeProduct,
    rlc_connectorOuter_numClusters_eq_pfd]
  ring


end
end StatMech.Universality
