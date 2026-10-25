/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

@[simp] theorem rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_pimsEdgeEquiv
        (rlc_twoChannelReflectedDualEdge gamma gamma' f) =
      Ising.kwg_embeddedEdge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f := by
  rw [rlc_twoChannelReflectedDualEdge,
    rlc_pimsEdgeEquiv_reflected_mk_of_adj
      (Ising.kwg_flanks_adj _ f), Ising.kwg_flanks_shared]


theorem rlc_twoChannelFullAmbientDual_reflectedEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_dualReflectConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
        (rlc_twoChannelReflectedDualEdge gamma gamma' f) =
      !(rlc_connectorForceTraceConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1) := by
  rw [rlc_dualReflectConfig_eq_pims,
    rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge,
    rlc_twoChannelFullAmbientConfig_embeddedEdge]


theorem rlc_twoChannelFullAmbientDual_reflectedEdge_open_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_dualReflectConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
          (rlc_twoChannelReflectedDualEdge gamma gamma' f) = true ↔
      f.1 ∉ (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).edgeSet := by
  rw [rlc_twoChannelFullAmbientDual_reflectedEdge]
  let forced := rlc_connectorForceTraceConfig gamma gamma'
    (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
  constructor
  · intro hopen hmem
    have htrue : forced f.1 = true := by
      induction hf : f.1 using Sym2.inductionOn with
      | _ x y =>
          rw [hf, SimpleGraph.mem_edgeSet, FK.openSub_adj] at hmem
          simpa [forced, hf] using hmem.2
    simp [forced, htrue] at hopen
  · intro hclosed
    have hfalse : forced f.1 = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      apply hclosed
      induction hf : f.1 using Sym2.inductionOn with
      | _ x y =>
          rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
          refine ⟨?_, ?_⟩
          · exact (SimpleGraph.mem_edgeSet _).mp (hf ▸ f.2)
          · simpa [forced, hf] using htrue
    simp [forced, hfalse]


theorem rlc_twoChannelFullAmbientConfig_open_mem_planarEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {e : Sym2 (Site 2)}
    (hopen : rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true) :
    e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  classical
  unfold rlc_twoChannelFullAmbientConfig at hopen
  split at hopen
  · rename_i hsource
    obtain ⟨f⟩ := hsource
    induction hf : f.1.1 using Sym2.inductionOn with
    | _ x y =>
        have htwo : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y := by
          have hfmem := f.1.2
          rw [hf, SimpleGraph.mem_edgeSet] at hfmem
          exact hfmem
        have hclosure :
            (rlc_connectorCentralFaceClosureGraph gamma gamma').Adj x y := by
          rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
          exact Or.inl htwo
        have heq : e = s((x : Site 2), (y : Site 2)) := by
          simpa [hf, Sym2.map_mk] using f.2.symm
        rw [heq]
        exact hclosure.2
  · rename_i hsource
    split at hopen
    · rename_i htrace
      rw [rlc_connectorCentralFacePlanarEdges,
        rlc_connectorFourTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ htrace)
    · simp at hopen


theorem rlc_openSub_twoChannelAugmented_forceTrace_eq_fullAmbientInduce
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)) =
      openSubgraphInduce 2
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
        (rect (-2 * n) (2 * n) (-n) n) := by
  classical
  ext x y
  change RlcConnectorVertex n at x y
  rw [FK.openSub_adj, openSubgraphInduce_adj]
  constructor
  · rintro ⟨hcarrier, hopen⟩
    let f : Ising.kwg_Edge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
      ⟨s(x, y), by
        rw [SimpleGraph.mem_edgeSet]
        exact hcarrier⟩
    have hf : f.1 = s(x, y) := rfl
    have hemb : Ising.kwg_embeddedEdge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f =
        s((x : Site 2), (y : Site 2)) := by
      rw [Ising.kwg_embeddedEdge, hf]
      rfl
    refine ⟨(rlc_connectorTwoChannelAugmentedPlanarDomain
      gamma gamma').isSub hcarrier, ?_⟩
    have hedge := rlc_twoChannelFullAmbientConfig_embeddedEdge
      gamma gamma' omega f
    rw [← hemb, hedge, hf]
    exact hopen
  · rintro ⟨hadj, hopen⟩
    have hplanar := rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
      gamma gamma' omega hopen
    have hcarrier :
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G.Adj x y := by
      rw [rlc_connectorTwoChannelAugmentedGraph_eq_closure]
      exact ⟨hadj, by simpa [Sym2.map_mk] using hplanar⟩
    refine ⟨hcarrier, ?_⟩
    let f : Ising.kwg_Edge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
      ⟨s(x, y), by
        rw [SimpleGraph.mem_edgeSet]
        exact hcarrier⟩
    have hf : f.1 = s(x, y) := rfl
    have hemb : Ising.kwg_embeddedEdge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f =
        s((x : Site 2), (y : Site 2)) := by
      rw [Ising.kwg_embeddedEdge, hf]
      rfl
    have hedge := rlc_twoChannelFullAmbientConfig_embeddedEdge
      gamma gamma' omega f
    calc
      rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) s(x, y) =
          rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1 :=
        congrArg _ hf.symm
      _ = rlc_twoChannelFullAmbientConfig gamma gamma' omega
          (Ising.kwg_embeddedEdge
            (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f) :=
        hedge.symm
      _ = rlc_twoChannelFullAmbientConfig gamma gamma' omega
          s((x : Site 2), (y : Site 2)) := congrArg _ hemb
      _ = true := hopen


end
end StatMech.Universality
