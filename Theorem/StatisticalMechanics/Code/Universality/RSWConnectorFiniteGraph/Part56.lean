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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part77
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCollaredOuterFaceProjection_edge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    (rlc_connectorCollaredOuterDualEdge gamma gamma' f).map
        (rlc_connectorCollaredOuterFaceProjection gamma gamma') =
      rlc_connectorCollaredDualEnds gamma gamma' f := by
  unfold rlc_connectorCollaredOuterDualEdge
  split
  · rename_i hret
    have hphysical := hret.choose_spec
    have hmapped := congrArg
      (Sym2.map (fun z : Site 2 => BeffaraDC.pfdFace
        (rlc_connectorCollaredPlanarDomain gamma gamma')
        (rlc_dualReflect.symm z))) hphysical
    simpa [rlc_connectorCollaredOuterTargetVertex,
      rlc_connectorCollaredOuterFaceProjection,
      rlc_connectorReflectedDualEdge,
      rlc_connectorCollaredDualEnds, Sym2.map_map] using hmapped
  · simp [rlc_connectorCollaredOuterPort,
      rlc_connectorCollaredOuterFaceProjection,
      rlc_connectorCollaredDualEnds]

theorem rlc_connectorCollaredOuterRandomGraph_adj_target {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    (rlc_connectorCollaredOuterRandomGraph gamma gamma').Adj
        (rlc_connectorCollaredOuterTargetVertex gamma gamma' x)
        (rlc_connectorCollaredOuterTargetVertex gamma gamma' y) ↔
      (rlc_connectorPIMSVariableGraph gamma gamma').Adj x y := by
  constructor
  · rintro ⟨_, f, hf⟩
    unfold rlc_connectorCollaredOuterDualEdge at hf
    split at hf
    · rename_i hret
      have hedge : hret.choose.1 = s(x, y) := by
        apply Sym2.map.injective
          (rlc_connectorCollaredOuterTargetVertex_injective gamma gamma')
        simpa [Sym2.map_mk,
          rlc_connectorCollaredOuterTargetVertex] using hf
      rw [← SimpleGraph.mem_edgeSet, ← hedge]
      exact hret.choose.2
    · rw [Sym2.eq_iff] at hf
      simp [rlc_connectorCollaredOuterTargetVertex,
        rlc_connectorCollaredOuterPort] at hf
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
      ⟨lifted, SimpleGraph.edgeSet_mono le_sup_left hlifted⟩
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
      (rlc_connectorCollaredOuterTargetVertex_injective
        gamma gamma' h), f, ?_⟩
    unfold rlc_connectorCollaredOuterDualEdge
    rw [dif_pos hret]
    have hedge : hret.choose.1 = targetEdge := by
      apply rlc_sym2Map_subtypeVal_injective
      exact hret.choose_spec.trans hreflected
    rw [hedge]
    rfl

theorem rlc_connectorCollaredOuterSpokeGraph_not_adj_targets {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    ¬(rlc_connectorCollaredOuterSpokeGraph gamma gamma').Adj
      (rlc_connectorCollaredOuterTargetVertex gamma gamma' x)
      (rlc_connectorCollaredOuterTargetVertex gamma gamma' y) := by
  rintro ⟨_, _, hghost⟩
  simp [RlcConnectorCollaredOuterIsFace,
    rlc_connectorCollaredOuterTargetVertex] at hghost


theorem rlc_connectorCollaredOuterDualGraph_adjMatch {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.ocd_AdjMatch
      (rlc_connectorPIMSVariableGraph gamma gamma')
      (rlc_connectorCollaredOuterDualGraph gamma gamma')
      (rlc_connectorCollaredOuterTargetVertex gamma gamma') := by
  intro x y
  rw [rlc_connectorCollaredOuterDualGraph, SimpleGraph.sup_adj]
  constructor
  · intro hxy
    exact Or.inl
      ((rlc_connectorCollaredOuterRandomGraph_adj_target
        gamma gamma' x y).2 hxy)
  · rintro (hrandom | hspoke)
    · exact (rlc_connectorCollaredOuterRandomGraph_adj_target
        gamma gamma' x y).1 hrandom
    · exact (rlc_connectorCollaredOuterSpokeGraph_not_adj_targets
        gamma gamma' x y hspoke).elim

end
end StatMech.Universality
