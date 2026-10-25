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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part19
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelPIMSPooledScoreHall_of_fullPhysicalSuccess
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess
      gamma gamma' hfaith)
    (N : Nat)
    (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect
      gamma gamma' N) :
    RlcTwoChannelEdgeCodeHall gamma gamma'
      (RlcTwoChannelPIMSPooledScoreCompatible hclosure N) := by
  rw [rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding]
  refine ⟨rlc_twoChannelFullPhysicalSuccessEmbedding hfaith hphysical, ?_⟩
  intro rho
  exact ⟨rlc_twoChannelFullPhysicalSuccessEmbedding_compatible
    hclosure hfaith hphysical rho, hscore rho⟩


theorem rlc_twoChannelFullPhysicalPermConfig_success_of_supportedWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y : Site 2}
    (hx : x ∈ rlc_pathVertices gamma.1)
    (hy : y ∈ rlc_pathVertices gamma'.1)
    (walk : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk x y)
    (hsupported : ∀ e ∈ walk.edges,
      ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        target.1.1.map Subtype.val = e) :
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  have hsupport : ∀ z ∈ walk.support,
      z ∈ rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
    rcases hz with rfl | ⟨e, he, hze⟩
    · exact rlc_leftPathVertex_mem_connectorBox gamma' hy
    · obtain ⟨target, htarget⟩ := hsupported e he
      induction hedge : target.1.1 using Sym2.inductionOn with
      | _ a b =>
          rw [hedge, Sym2.map_mk] at htarget
          rw [← htarget, Sym2.mem_iff] at hze
          rcases hze with rfl | rfl
          · exact a.2
          · exact b.2
  let liftVertex : walk.toSubgraph.verts → RlcConnectorVertex n :=
    fun z => ⟨z.1, hsupport z.1 (by
      rw [← walk.mem_verts_toSubgraph]
      exact z.2)⟩
  let hom : walk.toSubgraph.coe →g
      FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma'
          (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega)) :=
    { toFun := liftVertex
      map_rel' := by
        intro a b hab
        change walk.toSubgraph.Adj a.1 b.1 at hab
        have heWalk : s(a.1, b.1) ∈ walk.edges :=
          (walk.mem_edges_toSubgraph).mp
            ((SimpleGraph.mem_edgeSet walk.toSubgraph.spanningCoe).mpr hab)
        obtain ⟨target, htarget⟩ := hsupported s(a.1, b.1) heWalk
        have hedgeEq : target.1.1 = s(liftVertex a, liftVertex b) := by
          apply Sym2.map.injective Subtype.val_injective
          rw [htarget, Sym2.map_mk]
        rw [FK.openSub_adj]
        constructor
        · rw [← SimpleGraph.mem_edgeSet, ← hedgeEq]
          exact target.1.2
        · have hopenAmbient := walk.toSubgraph.adj_sub hab
          rw [openSubgraph_adj] at hopenAmbient
          have hfull :
              rlc_twoChannelFullDualConfig gamma gamma' omega
                  target.1.1 = true := by
            change rlc_dualReflectConfig
                (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
                (target.1.1.map Subtype.val) = true
            rw [htarget]
            exact hopenAmbient.2
          have hperm :
              rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega
                  target.1 = true := by
            rw [rlc_twoChannelFullPhysicalPermConfig_eq_fullDual]
            exact hfull
          change (if h : s(liftVertex a, liftVertex b) ∈
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
            rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega
              ⟨s(liftVertex a, liftVertex b), h⟩ else false) = true
          have hmem : s(liftVertex a, liftVertex b) ∈
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet := by
            rw [← hedgeEq]
            exact target.1.2
          rw [dif_pos hmem]
          have hsubtype :
              (⟨s(liftVertex a, liftVertex b), hmem⟩ :
                (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) =
                target.1 := by
            apply Subtype.ext
            exact hedgeEq.symm
          rw [hsubtype]
          exact hperm }
  let liftedWalk := walk.mapToSubgraph.map hom
  let xr : RlcConnectorVertex n :=
    ⟨x, rlc_rightPathVertex_mem_connectorBox gamma hx⟩
  let yl : RlcConnectorVertex n :=
    ⟨y, rlc_leftPathVertex_mem_connectorBox gamma' hy⟩
  refine ⟨xr, yl, hx, hy, ?_⟩
  have hreach : (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega))).Reachable
      (liftVertex ⟨x, walk.start_mem_verts_toSubgraph⟩)
      (liftVertex ⟨y, walk.end_mem_verts_toSubgraph⟩) :=
    ⟨liftedWalk⟩
  simpa [liftVertex, xr, yl] using hreach


end
end StatMech.Universality
