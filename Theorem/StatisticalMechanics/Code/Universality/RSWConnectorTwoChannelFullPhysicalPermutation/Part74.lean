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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part73
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalContactCycleCertificate_iff_goodComponent
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    RlcTwoChannelFullPhysicalContactCycleCertificate gamma gamma' omega ↔
      RlcTwoChannelFullPhysicalGoodComponentContacts
        gamma gamma' omega := by
  constructor
  · exact
      rlc_twoChannelFullPhysicalGoodComponentContacts_of_contactCycleCertificate
  · exact
      rlc_twoChannelFullPhysicalContactCycleCertificate_of_goodComponent
        hfaith


theorem rlc_twoChannelFullPhysicalContactCycleSelection_iff_goodComponents
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    RlcTwoChannelFullPhysicalContactCycleSelection gamma gamma' hfaith ↔
      ∀ omega : RlcTwoChannelEdgeConfig gamma gamma',
        rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
            rlc_finiteTwoChannelConnectorEvent gamma gamma' →
          RlcTwoChannelFullPhysicalGoodComponentContacts
            gamma gamma' omega := by
  constructor
  · intro hselection omega hno
    exact
      (rlc_twoChannelFullPhysicalContactCycleCertificate_iff_goodComponent
        hfaith omega).mp (hselection omega hno)
  · intro hcomponents omega hno
    exact
      (rlc_twoChannelFullPhysicalContactCycleCertificate_iff_goodComponent
        hfaith omega).mpr (hcomponents omega hno)


theorem rlc_twoChannelFullPhysicalFilledBoundarySegment_of_goodComponent
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hcomponent : RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega) :
    RlcTwoChannelFullPhysicalFilledBoundarySegment gamma gamma' omega := by
  obtain ⟨x, y, hxy, hx, hy⟩ := hcomponent
  obtain ⟨pGood⟩ := hxy
  let p := pGood.mapLe
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)
  refine ⟨x, y, p, hx, hy, ?_⟩
  intro e he
  have heGood : e ∈ pGood.edges := by
    simpa [p, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
  induction e using Sym2.inductionOn with
  | _ f g =>
      exact (pGood.adj_of_mem_edges heGood).2


theorem rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcRepairSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hrepair : RlcTwoChannelFullPhysicalContourArcRepairSide
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalFilledBoundarySegment
      gamma gamma' omega := by
  exact rlc_twoChannelFullPhysicalFilledBoundarySegment_of_goodComponent
    (rlc_twoChannelFullPhysical_goodComponent_of_contourArcRepairSide
      gamma gamma' omega c hx hy hxPath hyPath hrepair)


theorem rlc_twoChannelFullPhysicalPermConfig_success_of_filledBoundarySegment
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hsegment : RlcTwoChannelFullPhysicalFilledBoundarySegment
      gamma gamma' omega) :
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  obtain ⟨x, y, a, hx, hy, hsupported⟩ := hsegment
  let hle := rlc_twoChannelFullFilledBoundary_le_openFaceDual
    gamma gamma' omega
  let walk := rlc_dualReflectOpenWalk
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega) (a.mapLe hle)
  apply rlc_twoChannelFullPhysicalPermConfig_success_of_supportedWalk
    omega hx hy walk
  intro e he
  have hedges : walk.edges =
      (a.mapLe hle).edges.map
        (Sym2.map (rlc_dualReflectOpenHom
          (rlc_twoChannelFullAmbientConfig gamma gamma' omega))) :=
    SimpleGraph.Walk.edges_map
      (rlc_dualReflectOpenHom
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))
      (a.mapLe hle)
  rw [hedges] at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  have heA : e0 ∈ a.edges := by
    rwa [SimpleGraph.Walk.edges_mapLe_eq_edges] at he0
  obtain ⟨target, htarget⟩ := hsupported e0 heA
  refine ⟨target, ?_⟩
  simpa [rlc_dualReflectOpenHom] using htarget


theorem rlc_twoChannelFullPhysicalPermConfig_success_of_contourArcRepairSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hrepair : RlcTwoChannelFullPhysicalContourArcRepairSide
      gamma gamma' omega c hx hy) :
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  exact
    rlc_twoChannelFullPhysicalPermConfig_success_of_filledBoundarySegment
      omega
      (rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcRepairSide
        c hx hy hxPath hyPath hrepair)


end
end StatMech.Universality
