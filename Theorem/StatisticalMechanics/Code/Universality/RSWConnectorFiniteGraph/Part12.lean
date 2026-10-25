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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorAmbientCollaredConfig_connectorEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorEdges gamma gamma') :
    rlc_connectorAmbientCollaredConfig gamma gamma' tau e =
      tau (rlc_connectorEdgeLift gamma gamma' e he) := by
  simp [rlc_connectorAmbientCollaredConfig, he]

@[simp] theorem rlc_connectorAmbientCollaredConfig_traceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorAmbientCollaredConfig gamma gamma' tau e = true := by
  have hnot : e ∉ rlc_connectorEdges gamma gamma' := by
    rcases Finset.mem_union.mp he with hright | hleft
    · exact Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_connector gamma gamma') hright
    · exact Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_connector gamma gamma') hleft
  have hforced : e ∈
      (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
        rlc_connectorPIMSExteriorPreimages gamma gamma' :=
    Finset.mem_union_left _ he
  rw [rlc_connectorAmbientCollaredConfig, dif_neg hnot, if_pos hforced]

@[simp] theorem rlc_connectorAmbientCollaredConfig_collarEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorPIMSExteriorPreimages gamma gamma') :
    rlc_connectorAmbientCollaredConfig gamma gamma' tau e = true := by
  have hnotUnion : e ∉ rlc_connectorEdges gamma gamma' ∪
      (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :=
    (Finset.mem_sdiff.mp he).2
  have hnot : e ∉ rlc_connectorEdges gamma gamma' :=
    fun h => hnotUnion (Finset.mem_union_left _ h)
  have hforced : e ∈
      (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
        rlc_connectorPIMSExteriorPreimages gamma gamma' :=
    Finset.mem_union_right _ he
  rw [rlc_connectorAmbientCollaredConfig, dif_neg hnot, if_pos hforced]

theorem rlc_sym2Map_subtypeVal_injective {n : Int} :
    Function.Injective
      (Sym2.map (Subtype.val : RlcConnectorVertex n → Site 2)) := by
  intro e f hef
  induction e using Sym2.inductionOn with
  | _ x y =>
      induction f using Sym2.inductionOn with
      | _ u v =>
          simp only [Sym2.map_mk] at hef
          rw [Sym2.eq_iff] at hef ⊢
          rcases hef with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · exact Or.inl ⟨Subtype.ext hxu, Subtype.ext hyv⟩
          · exact Or.inr ⟨Subtype.ext hxv, Subtype.ext hyu⟩


theorem rlc_connectorAmbientMixedConfig_graphEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_connectorFiniteGraph gamma gamma').Adj x y) :
    rlc_connectorRestrictConfig
        (rlc_connectorAmbientMixedConfig gamma gamma' tau) s(x, y) =
      tau s(x, y) := by
  have he : s((x : Site 2), (y : Site 2)) ∈
      rlc_connectorEdges gamma gamma' := hxy.2
  rw [rlc_connectorRestrictConfig, Sym2.map_mk,
    rlc_connectorAmbientMixedConfig_connectorEdge gamma gamma' tau he]
  congr 1
  apply rlc_sym2Map_subtypeVal_injective
  rw [rlc_connectorEdgeLift_map]
  rfl

theorem rlc_openSub_restrict_ambientMixed_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorRestrictConfig
          (rlc_connectorAmbientMixedConfig gamma gamma' tau)) =
      FK.openSub (rlc_connectorFiniteGraph gamma gamma') tau := by
  ext x y
  simp only [FK.openSub_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    exact ⟨hxy, by
      rw [rlc_connectorAmbientMixedConfig_graphEdge gamma gamma' tau hxy] at hopen
      exact hopen⟩
  · rintro ⟨hxy, hopen⟩
    exact ⟨hxy, by
      rw [rlc_connectorAmbientMixedConfig_graphEdge gamma gamma' tau hxy]
      exact hopen⟩


end
end StatMech.Universality
