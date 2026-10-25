/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part44
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelForceTrace_sourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : RlcTwoChannelFaithfulSourceEdge gamma gamma') :
    rlc_connectorForceTraceConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
        (rlc_twoChannelFaithfulAugmentedEdge e).1 = omega e := by
  induction he : e.1 using Sym2.inductionOn with
  | _ x y =>
      have htwo : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp (he ▸ e.2)
      have hnotTrace : s(x, y) ∉
          (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
        intro hmem
        exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp
          (SimpleGraph.mem_edgeFinset.mp hmem))
      change rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) e.1 = omega e
      rw [he]
      change (if s(x, y) ∈
          (rlc_connectorTraceWiring gamma gamma').edgeFinset then true
        else rlc_twoChannelEdgeConfigExtend gamma gamma' omega s(x, y)) =
          omega e
      calc
        _ = rlc_twoChannelEdgeConfigExtend gamma gamma' omega s(x, y) :=
          if_neg hnotTrace
        _ = omega e := by
          change (if h : s(x, y) ∈
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
            omega ⟨s(x, y), h⟩ else false) = omega e
          have hs : s(x, y) ∈
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
            (SimpleGraph.mem_edgeSet _).mpr htwo
          rw [dif_pos hs]
          congr 1
          exact Subtype.ext he.symm

theorem rlc_twoChannelFaithfulDualConfig_open_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : RlcTwoChannelFaithfulSourceEdge gamma gamma') :
    rlc_twoChannelFaithfulDualConfig gamma gamma' omega e = true ↔
      (rlc_twoChannelFaithfulAugmentedEdge e).1 ∉
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).edgeSet := by
  have h := rlc_twoChannelFullAmbientDual_reflectedEdge_open_iff
    gamma gamma' omega (rlc_twoChannelFaithfulAugmentedEdge e)
  rw [rlc_twoChannelFullAmbientDual_reflectedEdge,
    rlc_twoChannelForceTrace_sourceEdge] at h
  exact h


theorem rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.indexedOpenGraph (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) =
      BeffaraDC.pfdClosedDual
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) := by
  ext C D
  simp only [FK.indexedOpenGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_setOf_eq, BeffaraDC.pfdClosedDual_adj]
  constructor
  · rintro ⟨⟨e, hends, hopen⟩, hne⟩
    exact ⟨hne, rlc_twoChannelFaithfulAugmentedEdge e,
      (rlc_twoChannelFaithfulDualConfig_open_iff
        gamma gamma' omega e).mp hopen, hends⟩
  · rintro ⟨hne, f, hfclosed, hends⟩
    induction hedge : f.1 using Sym2.inductionOn with
    | _ x y =>
        have hfmem := f.2
        rw [hedge, SimpleGraph.mem_edgeSet] at hfmem
        change (rlc_connectorTwoChannelGraph gamma gamma' ⊔
          rlc_connectorTraceWiring gamma gamma').Adj x y at hfmem
        rcases hfmem with htwo | htrace
        · let e : RlcTwoChannelFaithfulSourceEdge gamma gamma' :=
            ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
          have hf : rlc_twoChannelFaithfulAugmentedEdge e = f := by
            apply Subtype.ext
            exact hedge.symm
          refine ⟨⟨e, ?_, ?_⟩, hne⟩
          · change Ising.kwg_dualEnds
                (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
                (rlc_twoChannelFaithfulAugmentedEdge e) = s(C, D)
            rw [hf]
            exact hends
          · apply (rlc_twoChannelFaithfulDualConfig_open_iff
              gamma gamma' omega e).mpr
            simpa [hf] using hfclosed
        · exfalso
          apply hfclosed
          rw [hedge, SimpleGraph.mem_edgeSet, FK.openSub_adj]
          refine ⟨Or.inr htrace, ?_⟩
          have hmem : s(x, y) ∈
              (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
            SimpleGraph.mem_edgeFinset.mpr
              ((SimpleGraph.mem_edgeSet _).mpr htrace)
          change rlc_connectorForceTraceConfig gamma gamma'
              (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
              s(x, y) = true
          exact if_pos hmem


theorem rlc_twoChannelFullFaceDual_le_pfdRegion {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    openSubgraph 2 (fci_faceDualConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) ≤
      whb_faceRegion (jei_pushGraph
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))) := by
  classical
  intro f g hfg
  have hface : (fci_faceOpenDual
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega)).Adj f g := by
    rw [fci_faceOpenDual_eq_openSubgraph]
    exact hfg
  rw [fci_faceOpenDual_adj] at hface
  rw [whb_faceRegion_adj]
  refine ⟨hface.1, ?_⟩
  intro hmem
  induction hshared : sharedPrimalEdge f g using Sym2.inductionOn with
  | _ a b =>
      rw [hshared, SimpleGraph.mem_edgeSet, jei_pushGraph_adj] at hmem
      obtain ⟨x, y, hxy, hx, hy⟩ := hmem
      rw [FK.openSub_adj] at hxy
      let e : Ising.kwg_Edge
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
        ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hxy.1⟩
      have hemb : Ising.kwg_embeddedEdge
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') e =
          sharedPrimalEdge f g := by
        rw [hshared, Ising.kwg_embeddedEdge, Sym2.map_mk]
        rw [hx, hy]
      have hopen := rlc_twoChannelFullAmbientConfig_embeddedEdge
        gamma gamma' omega e
      rw [hemb] at hopen
      have hamb : rlc_twoChannelFullAmbientConfig gamma gamma' omega
          (sharedPrimalEdge f g) = true := hopen.trans hxy.2
      rw [hamb] at hface
      exact Bool.noConfusion hface.2


theorem rlc_twoChannelFullFaceDual_eq_pfdRegion {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    openSubgraph 2 (fci_faceDualConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) =
      whb_faceRegion (jei_pushGraph
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))) := by
  apply le_antisymm
  · exact rlc_twoChannelFullFaceDual_le_pfdRegion gamma gamma' omega
  · classical
    intro f g hfg
    rw [whb_faceRegion_adj] at hfg
    rw [← fci_faceOpenDual_eq_openSubgraph, fci_faceOpenDual_adj]
    refine ⟨hfg.1, Bool.eq_false_of_not_eq_true ?_⟩
    intro hopen
    have hplanar := rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
      gamma gamma' omega hopen
    induction hshared : sharedPrimalEdge f g using Sym2.inductionOn with
    | _ a b =>
        have haBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
          gamma gamma' hplanar (hshared ▸ Sym2.mem_mk_left a b)
        have hbBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
          gamma gamma' hplanar (hshared ▸ Sym2.mem_mk_right a b)
        let x : RlcConnectorVertex n := ⟨a, by
          simpa [RlcConnectorVertex, rlc_connectorBox] using haBox⟩
        let y : RlcConnectorVertex n := ⟨b, by
          simpa [RlcConnectorVertex, rlc_connectorBox] using hbBox⟩
        obtain ⟨p, q, hpq, hpqAdj⟩ :=
          sharedPrimalEdge_isLatticeEdge hfg.1
        have habPair : s(a, b) = s(p, q) := hshared.symm.trans hpq
        rw [Sym2.eq_iff] at habPair
        have hab : (hypercubicLattice 2).Adj a b := by
          rcases habPair with habPair | habPair
          · simpa [habPair.1, habPair.2] using hpqAdj
          · simpa [habPair.1, habPair.2] using hpqAdj.symm
        have hcarrier :
            (rlc_connectorTwoChannelAugmentedPlanarDomain
              gamma gamma').G.Adj x y := by
          rw [rlc_connectorTwoChannelAugmentedGraph_eq_closure]
          exact ⟨hab, by simpa [x, y, hshared] using hplanar⟩
        let e : Ising.kwg_Edge
            (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
          ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hcarrier⟩
        have hemb : Ising.kwg_embeddedEdge
            (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') e =
              sharedPrimalEdge f g := by
          rw [hshared, Ising.kwg_embeddedEdge, Sym2.map_mk]
          rfl
        have hedge := rlc_twoChannelFullAmbientConfig_embeddedEdge
          gamma gamma' omega e
        rw [hemb, hopen] at hedge
        have hK : (FK.openSub
            (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
            (rlc_connectorForceTraceConfig gamma gamma'
              (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).Adj x y :=
          ⟨hcarrier, by simpa [e] using hedge.symm⟩
        apply hfg.2
        rw [hshared, SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
        exact ⟨x, y, hK, rfl, rfl⟩


theorem rlc_twoChannelFaithful_indexedNumClusters_eq_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.indexedNumClustersBC (rlc_twoChannelFaithfulEnds gamma gamma') ⊥
        (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) =
      Nat.card (BeffaraDC.pfdClosedDual
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).ConnectedComponent := by
  unfold FK.indexedNumClustersBC
  rw [sup_bot_eq,
    rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual]


theorem rlc_twoChannelFaithful_indexedEdgeProduct_eq_source {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.edgeProduct (rlc_connectorTwoChannelGraph gamma gamma') (1 - p)
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) =
      FK.indexedEdgeProduct p
        (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
  classical
  unfold FK.edgeProduct FK.indexedEdgeProduct
  rw [← Finset.prod_attach
    (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset,
    Finset.attach_eq_univ]
  let edgeEquiv :
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset ≃
        RlcTwoChannelFaithfulSourceEdge gamma gamma' :=
    { toFun := fun e => ⟨e.1, by
          simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      invFun := fun e => ⟨e.1, by
          simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      left_inv := by intro e; rfl
      right_inv := by intro e; rfl }
  apply Fintype.prod_equiv edgeEquiv
  intro e
  have hext : rlc_twoChannelEdgeConfigExtend gamma gamma' omega e.1 =
      omega (edgeEquiv e) := by
    change rlc_twoChannelEdgeConfigCombine gamma gamma' omega
        (fun _ => false) e.1 = omega (edgeEquiv e)
    exact rlc_twoChannelEdgeConfigCombine_edge gamma gamma' omega
      (fun _ => false) (edgeEquiv e)
  rw [hext]
  cases h : omega (edgeEquiv e) <;>
    simp [h, rlc_twoChannelFaithfulDualConfig]


theorem rlc_twoChannelFaithful_pfdDualEdgeFactor_eq_indexed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
    let forced := rlc_connectorForceTraceConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
    BeffaraDC.edgeProductCount p P.G.edgeFinset.card
        (P.G.edgeFinset.card -
          (FK.openSub P.G forced).edgeSet.ncard) =
      (1 - p) ^
          (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.indexedEdgeProduct p
          (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
  dsimp only
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let forced := rlc_connectorForceTraceConfig gamma gamma'
    (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
  calc
    BeffaraDC.edgeProductCount p P.G.edgeFinset.card
        (P.G.edgeFinset.card -
          (FK.openSub P.G forced).edgeSet.ncard) =
      BeffaraDC.edgeProductCount p P.G.edgeFinset.card
        (FK.openCount P.G (fun e => !(forced e))) := by
          rw [rlc_openCount_complement,
            BeffaraDC.pfd_openSub_edge_ncard]
    _ = FK.edgeProduct P.G p (fun e => !(forced e)) :=
      (BeffaraDC.dlt_edgeProduct_eq_count P.G p
        (fun e => !(forced e))).symm
    _ = FK.edgeProduct P.G (1 - p) forced := by
      unfold FK.edgeProduct
      apply Finset.prod_congr rfl
      intro e _
      cases h : forced e <;> simp [h]
    _ = (1 - p) ^
          (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.edgeProduct (rlc_connectorTwoChannelGraph gamma gamma') (1 - p)
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
      exact rlc_twoChannel_edgeProduct_augmented_forceTrace
        gamma gamma' (1 - p)
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
    _ = (1 - p) ^
          (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.indexedEdgeProduct p
          (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
      rw [rlc_twoChannelFaithful_indexedEdgeProduct_eq_source]


theorem rlc_twoChannelFaithful_pfdDualWeight_eq_indexed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    BeffaraDC.pfdDualWeight
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) =
      (1 - p) ^
          (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.indexedBcWeight (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q
          (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
  unfold BeffaraDC.pfdDualWeight FK.indexedBcWeight
  rw [rlc_twoChannelFaithful_pfdDualEdgeFactor_eq_indexed,
    rlc_twoChannelFaithful_indexedNumClusters_eq_pfd]
  ring


end
end StatMech.Universality
