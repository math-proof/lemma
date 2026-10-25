/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part67
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_prefix_not_all_fourTrace_iff_exists_nonWallEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u) :
    (¬∀ e ∈ q.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ↔
      ∃ e ∈ q.edges,
        Sym2.map rlc_dualReflect e ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
  constructor
  · intro h
    push Not at h
    exact h
  · rintro ⟨e, he, hnot⟩ hall
    exact hnot (hall e he)


theorem
    rlc_twoChannelFullPhysical_rightNonWallPrefix_staticCutReach
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {x u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x u)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hbranch : ∃ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∉
        rlc_connectorFourTraceEdges gamma gamma') :
    ∃ f g : Site 2,
      s(f, g) ∈ q.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_connectorOnRight gamma
          (rlc_twoChannelFullPhysicalLiftFace gamma x) ∧
        (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable
          (rlc_twoChannelFullPhysicalLiftFace gamma x)
          (rlc_twoChannelFullPhysicalLiftFace gamma f) ∧
        (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Adj
          (rlc_twoChannelFullPhysicalLiftFace gamma f)
          (rlc_twoChannelFullPhysicalLiftFace gamma g) := by
  obtain ⟨e, he, hnot⟩ := hbranch
  induction e using Sym2.inductionOn with
  | _ f g =>
      have hfg := q.adj_of_mem_edges he
      have hfSupport := q.fst_mem_support_of_mem_edges he
      have hreachGood :
          (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Reachable
              x f := ⟨q.takeUntil f hfSupport⟩
      have hxBox : rlc_dualReflect x ∈
          rect (-2 * n) (2 * n) (-n) n :=
        rlc_rightPathVertex_mem_connectorBox gamma hxPath
      refine ⟨f, g, he, ?_, ?_, ?_, ?_⟩
      · simpa [Sym2.map_mk] using hnot
      · simpa [rlc_twoChannelFullPhysicalLiftFace_of_mem gamma x hxBox,
          rlc_connectorOnRight] using hxPath
      · exact
          rlc_twoChannelFullPhysical_goodBoundary_reachable_staticCutTarget
            gamma gamma' A hAright hAleft hreachGood
      · exact rlc_twoChannelFullPhysical_goodBoundary_le_staticCutTarget
          gamma gamma' A hAright hAleft hfg


theorem
    rlc_twoChannelFullPhysical_leftNonWallPrefix_staticCutReach
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {y u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y u)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hbranch : ∃ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∉
        rlc_connectorFourTraceEdges gamma gamma') :
    ∃ f g : Site 2,
      s(f, g) ∈ q.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_connectorOnLeft gamma'
          (rlc_twoChannelFullPhysicalLiftFace gamma y) ∧
        (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable
          (rlc_twoChannelFullPhysicalLiftFace gamma y)
          (rlc_twoChannelFullPhysicalLiftFace gamma f) ∧
        (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Adj
          (rlc_twoChannelFullPhysicalLiftFace gamma f)
          (rlc_twoChannelFullPhysicalLiftFace gamma g) := by
  obtain ⟨e, he, hnot⟩ := hbranch
  induction e using Sym2.inductionOn with
  | _ f g =>
      have hfg := q.adj_of_mem_edges he
      have hfSupport := q.fst_mem_support_of_mem_edges he
      have hreachGood :
          (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Reachable
              y f := ⟨q.takeUntil f hfSupport⟩
      have hyBox : rlc_dualReflect y ∈
          rect (-2 * n) (2 * n) (-n) n :=
        rlc_leftPathVertex_mem_connectorBox gamma' hyPath
      refine ⟨f, g, he, ?_, ?_, ?_, ?_⟩
      · simpa [Sym2.map_mk] using hnot
      · simpa [rlc_twoChannelFullPhysicalLiftFace_of_mem gamma y hyBox,
          rlc_connectorOnLeft] using hyPath
      · exact
          rlc_twoChannelFullPhysical_goodBoundary_reachable_staticCutTarget
            gamma gamma' A hAright hAleft hreachGood
      · exact rlc_twoChannelFullPhysical_goodBoundary_le_staticCutTarget
          gamma gamma' A hAright hAleft hfg


end
end StatMech.Universality
