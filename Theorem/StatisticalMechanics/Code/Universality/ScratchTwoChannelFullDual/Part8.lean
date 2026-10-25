/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelFullFilledBoundaryContacts gamma gamma' omega := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  obtain ⟨z, hzRight, hzFlipLeft⟩ :=
    rlc_bookFlippedTraceIntersection_of_faithful gamma gamma' hfaith
  have hrightStartFlip :
      rlc_flipX (gamma.1.1 : Site 2) = (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  have hrightStartH : rlc_flipX (gamma.1.1 : Site 2) ∈ H := by
    rw [hrightStartFlip]
    exact rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
      (rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega
        (rlc_path_start_mem_vertices gamma.1))
  have hzFlipExt :=
    rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hzFlipLeft
  have hzFlipOut : rlc_flipX z ∉ H := by
    simpa [H, rlc_twoChannelFullFilledReachSet] using hzFlipExt
  obtain ⟨x, hxSupp, hxPath⟩ :=
    rlc_faceBoundary_contact_of_flippedTrace_exit gamma.1 H
      (rlc_path_start_mem_vertices gamma.1) hrightStartH hzRight hzFlipOut
  let u : Site 2 := rlc_flipX z
  have huLeft : u ∈ rlc_pathVertices gamma'.1 := hzFlipLeft
  have huFlipH : rlc_flipX u ∈ H := by
    have huFlip : rlc_flipX u = z := by simp [u]
    rw [huFlip]
    exact rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
      (rlc_rightPathVertex_mem_twoChannelFullReachSet
        gamma gamma' omega hzRight)
  have hleftEndPath : (gamma'.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    rlc_connector_path_end_mem_vertices gamma'.1
  have hleftEndExt :=
    rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hleftEndPath
  have hleftEndFlip :
      rlc_flipX (gamma'.1.2.1 : Site 2) =
        (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hleftEndOut : rlc_flipX (gamma'.1.2.1 : Site 2) ∉ H := by
    rw [hleftEndFlip]
    simpa [H, rlc_twoChannelFullFilledReachSet] using hleftEndExt
  obtain ⟨y, hySupp, hyPath⟩ :=
    rlc_faceBoundary_contact_of_flippedTrace_exit gamma'.1 H
      huLeft huFlipH hleftEndPath hleftEndOut
  exact ⟨x, y, hxSupp, hySupp, hxPath, hyPath⟩


theorem rlc_twoChannelFullFilledFaceBoundary_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {f g : Site 2}
    (hf : f ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (hg : g ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable f g := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  let hH := rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega
  have hconn := rlc_twoChannelFullFilledReachSet_faceBoundaryConnected
    gamma gamma' omega
  rw [FaceBoundaryConnected, SimpleGraph.connected_iff] at hconn
  have hfT : f ∈ phb_boundarySupport H hH := by simpa [H, hH] using hf
  have hgT : g ∈ phb_boundarySupport H hH := by simpa [H, hH] using hg
  have hreach := hconn.1 ⟨f, hfT⟩ ⟨g, hgT⟩
  exact hreach.map (SimpleGraph.Embedding.induce
    (phb_boundarySupport H hH : Set (Site 2))).toHom


theorem rlc_twoChannelFull_reflectedOpenDualWalk_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ x y : Site 2,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      Nonempty ((openSubgraph 2 (rlc_dualReflectConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk
          (rlc_dualReflect x) (rlc_dualReflect y)) := by
  obtain ⟨x, y, hx, hy, hxPath, hyPath⟩ :=
    rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith omega hno
  obtain ⟨a⟩ := rlc_twoChannelFullFilledFaceBoundary_reachable
    gamma gamma' omega hx hy
  let hle := rlc_twoChannelFullFilledBoundary_le_openFaceDual
    gamma gamma' omega
  exact ⟨x, y, hxPath, hyPath,
    ⟨rlc_dualReflectOpenWalk _ (a.mapLe hle)⟩⟩


end
end StatMech.Universality
