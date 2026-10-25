/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCentralFaceFiniteGraph_le_twoChannel {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorCentralFaceFiniteGraph gamma gamma' ≤
      rlc_connectorTwoChannelGraph gamma gamma' :=
  by
    intro x y hxy
    refine ⟨Or.inl hxy, ?_⟩
    intro htrace
    apply Finset.disjoint_left.mp
      (rlc_connectorCentralFaceEdges_disjoint_fourTrace gamma gamma')
      hxy.2
    exact Finset.mem_union_left _ htrace.2

theorem rlc_finiteCentralFaceRandomConnectorEvent_subset_twoChannel
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    rlc_finiteCentralFaceRandomConnectorEvent gamma gamma' ⊆
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  rintro rho ⟨x, y, hx, hy, hxy⟩
  refine ⟨x, y, hx, hy, hxy.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  exact ⟨rlc_connectorCentralFaceFiniteGraph_le_twoChannel
    gamma gamma' huv.1, huv.2⟩


theorem rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorCentralFaceClosureGraph gamma gamma' =
      rlc_connectorTwoChannelGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma' := by
  ext x y
  simp only [rlc_connectorCentralFaceClosureGraph,
    rlc_connectorTwoChannelGraph, rlc_connectorCentralFaceFiniteGraph,
    rlc_connectorReflectedTraceWiring, rlc_connectorTraceWiring,
    SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hxy, hedge⟩
    rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union] at hedge
    rcases hedge with hclosure | hfour
    · by_cases hwall : s((x : Site 2), (y : Site 2)) ∈
          rlc_connectorFourTraceEdges gamma gamma'
      · rw [rlc_connectorFourTraceEdges, Finset.mem_union] at hwall
        rcases hwall with horiginal | hreflected
        · exact Or.inr ⟨hxy, horiginal⟩
        · by_cases horiginal : s((x : Site 2), (y : Site 2)) ∈
              rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
          · exact Or.inr ⟨hxy, horiginal⟩
          · exact Or.inl ⟨Or.inr ⟨hxy, hreflected⟩,
              fun htrace => horiginal htrace.2⟩
      · exact Or.inl ⟨Or.inl ⟨hxy,
          Finset.mem_sdiff.mpr ⟨hclosure, hwall⟩⟩, fun htrace =>
            hwall (Finset.mem_union_left _ htrace.2)⟩
    · rw [rlc_connectorFourTraceEdges, Finset.mem_union] at hfour
      rcases hfour with horiginal | hreflected
      · exact Or.inr ⟨hxy, horiginal⟩
      · by_cases horiginal : s((x : Site 2), (y : Site 2)) ∈
            rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
        · exact Or.inr ⟨hxy, horiginal⟩
        · exact Or.inl ⟨Or.inr ⟨hxy, hreflected⟩,
            fun htrace => horiginal htrace.2⟩
  · rintro (htwo | htrace)
    · rcases htwo with ⟨hchannel, _hnot⟩
      rcases hchannel with ⟨hxy, hcentral⟩ | ⟨hxy, hreflected⟩
      · exact ⟨hxy, Finset.mem_union_left _
          (Finset.mem_sdiff.mp hcentral).1⟩
      · exact ⟨hxy, Finset.mem_union_right _ <|
          Finset.mem_union_right _ hreflected⟩
    · rcases htrace with ⟨hxy, horiginal⟩
      exact ⟨hxy, Finset.mem_union_right _ <|
        Finset.mem_union_left _ horiginal⟩


end
end StatMech.Universality
