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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part42
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorAugmentedEdgeToCollared_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_connectorAugmentedEdgeToCollared gamma gamma') := by
  intro e f hef
  apply Subtype.ext
  exact Sym2.map.injective
    (rlc_connectorVertexToCollared_injective gamma gamma')
    (congrArg Subtype.val hef)


theorem rlc_connectorCollaredWall_mem_imageGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCollaredWallEdges gamma gamma')
    (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
    e ∈ (Lattice.imageGraph
      (rlc_connectorCollaredPlanarDomain gamma gamma')).edgeSet := by
  induction hedge : e using Sym2.inductionOn with
  | _ u v =>
    have hu : u ∈ e := by rw [hedge]; simp
    have hv : v ∈ e := by rw [hedge]; simp
    let x : RlcConnectorCollaredVertex gamma gamma' :=
      ⟨u, rlc_connectorCollaredWall_endpoint_mem gamma gamma' he hu⟩
    let y : RlcConnectorCollaredVertex gamma gamma' :=
      ⟨v, rlc_connectorCollaredWall_endpoint_mem gamma gamma' he hv⟩
    rw [SimpleGraph.mem_edgeSet, Lattice.imageGraph_adj]
    refine ⟨x, y, ⟨?_, ?_⟩, rfl, rfl⟩
    · exact (SimpleGraph.mem_edgeSet _).mp (hedge ▸ hlat)
    · simpa [x, y] using (hedge ▸ he)


theorem rlc_connectorCollaredWall_blocks_faceStep {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCollaredWallEdges gamma gamma')
    (hlat : e ∈ (hypercubicLattice 2).edgeSet)
    {f g : Site 2}
    (hshared : sharedPrimalEdge f g = e) :
    ¬ (whb_faceRegion (Lattice.imageGraph
      (rlc_connectorCollaredPlanarDomain gamma gamma'))).Adj f g := by
  intro hface
  have hnot := (whb_faceRegion_adj _ f g).mp hface |>.2
  apply hnot
  rw [hshared]
  exact rlc_connectorCollaredWall_mem_imageGraph
    gamma gamma' he hlat


theorem rlc_connectorCollared_preimage_blocks_faceStep {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (htarget : e ∈ rlc_connectorEdges gamma gamma')
    (htargetLat : e ∈ (hypercubicLattice 2).edgeSet)
    (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
    {f g : Site 2}
    (hshared : sharedPrimalEdge f g = rlc_pimsEdgeEquiv e) :
    ¬ (whb_faceRegion (Lattice.imageGraph
      (rlc_connectorCollaredPlanarDomain gamma gamma'))).Adj f g := by
  apply rlc_connectorCollaredWall_blocks_faceStep gamma gamma'
    (rlc_connectorCollaredWallEdges_preimage
      gamma gamma' htarget hsource htrace)
    (rlc_pimsEdgeEquiv_mem_latticeEdge htargetLat) hshared


theorem rlc_connectorEdgeLift_mem_finiteGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : Sym2 (Site 2)) (he : e ∈ rlc_connectorEdges gamma gamma')
    (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
    rlc_connectorEdgeLift gamma gamma' e he ∈
      (rlc_connectorFiniteGraph gamma gamma').edgeSet := by
  have hmap := rlc_connectorEdgeLift_map gamma gamma' e he
  revert hmap
  induction rlc_connectorEdgeLift gamma gamma' e he using
      Sym2.inductionOn with
  | _ x y =>
      intro hmap
      rw [Sym2.map_mk] at hmap
      rw [SimpleGraph.mem_edgeSet]
      refine ⟨?_, ?_⟩
      · apply (SimpleGraph.mem_edgeSet _).mp
        rw [hmap]
        exact hlat
      · rw [hmap]
        exact he


theorem rlc_connectorOuterRandomGraph_adj_target {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    (rlc_connectorOuterRandomGraph gamma gamma').Adj
        (rlc_connectorOuterTargetVertex gamma gamma' x)
        (rlc_connectorOuterTargetVertex gamma gamma' y) ↔
      (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y := by
  constructor
  · rintro ⟨_, f, hf⟩
    unfold rlc_connectorOuterDualEdge at hf
    split at hf
    · rename_i hret
      have hedge : hret.choose.1 = s(x, y) := by
        apply Sym2.map.injective
          (rlc_connectorOuterTargetVertex_injective gamma gamma')
        simpa [Sym2.map_mk, rlc_connectorOuterTargetVertex] using hf
      rw [← SimpleGraph.mem_edgeSet]
      rw [← hedge]
      exact hret.choose.2
    · rw [Sym2.eq_iff] at hf
      simp [rlc_connectorOuterTargetVertex,
        rlc_connectorOuterPort] at hf
  · intro hxy
    let targetEdge : Sym2 (RlcConnectorVertex n) := s(x, y)
    let sourceEdge : Sym2 (Site 2) :=
      rlc_pimsEdgeEquiv (targetEdge.map Subtype.val)
    have hsource : sourceEdge ∈ rlc_connectorEdges gamma gamma' :=
      hxy.2
    have htargetLat : targetEdge.map Subtype.val ∈
        (hypercubicLattice 2).edgeSet := by
      change s((x : Site 2), (y : Site 2)) ∈
        (hypercubicLattice 2).edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact hxy.1.1
    have hsourceLat : sourceEdge ∈ (hypercubicLattice 2).edgeSet :=
      rlc_pimsEdgeEquiv_mem_latticeEdge htargetLat
    let lifted := rlc_connectorEdgeLift gamma gamma' sourceEdge hsource
    have hlifted : lifted ∈
        (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
      rlc_connectorEdgeLift_mem_finiteGraph gamma gamma'
        sourceEdge hsource hsourceLat
    let f : Ising.kwg_Edge
        (rlc_connectorAugmentedPlanarDomain gamma gamma') :=
      ⟨lifted, by
        change lifted ∈
          (rlc_connectorFiniteGraph gamma gamma' ⊔
            rlc_connectorTraceWiring gamma gamma').edgeSet
        exact SimpleGraph.edgeSet_mono le_sup_left hlifted⟩
    have hreflected :
        rlc_connectorReflectedDualEdge gamma gamma' f =
          targetEdge.map Subtype.val := by
      apply rlc_pimsEdgeEquiv.injective
      rw [rlc_pimsEdgeEquiv_connectorReflectedDualEdge]
      change lifted.map Subtype.val = sourceEdge
      exact rlc_connectorEdgeLift_map gamma gamma' sourceEdge hsource
    have hret : RlcConnectorRetainedDualEdge gamma gamma' f := by
      refine ⟨⟨targetEdge, ?_⟩, hreflected.symm⟩
      rw [SimpleGraph.mem_edgeSet]
      exact hxy
    refine ⟨fun h => hxy.ne
      (rlc_connectorOuterTargetVertex_injective gamma gamma' h), f, ?_⟩
    unfold rlc_connectorOuterDualEdge
    rw [dif_pos hret]
    have hedge : hret.choose.1 = targetEdge := by
      apply rlc_sym2Map_subtypeVal_injective
      exact hret.choose_spec.trans hreflected
    rw [hedge]
    rfl


theorem rlc_connectorOuterSpokeGraph_not_adj_targets {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    ¬(rlc_connectorOuterSpokeGraph gamma gamma').Adj
      (rlc_connectorOuterTargetVertex gamma gamma' x)
      (rlc_connectorOuterTargetVertex gamma gamma' y) := by
  rintro ⟨_, _, hghost⟩
  simp [RlcConnectorOuterIsFace,
    rlc_connectorOuterTargetVertex] at hghost


theorem rlc_connectorOuterDualGraph_adjMatch {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.ocd_AdjMatch
      (rlc_connectorPIMSVariableGraph gamma gamma')
      (rlc_connectorOuterDualGraph gamma gamma')
      (rlc_connectorOuterTargetVertex gamma gamma') := by
  intro x y
  rw [rlc_connectorOuterDualGraph, SimpleGraph.sup_adj]
  constructor
  · intro hxy
    exact Or.inl
      ((rlc_connectorOuterRandomGraph_adj_target gamma gamma' x y).2 hxy)
  · rintro (hrandom | hspoke)
    · exact (rlc_connectorOuterRandomGraph_adj_target gamma gamma' x y).1
        hrandom
    · exact (rlc_connectorOuterSpokeGraph_not_adj_targets
        gamma gamma' x y hspoke).elim


end
end StatMech.Universality
