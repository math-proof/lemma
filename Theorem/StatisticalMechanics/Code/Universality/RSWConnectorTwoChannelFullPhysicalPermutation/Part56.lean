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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part56
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_noGood_rightLeftPrefixes_disjoint
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {x y ur ul : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul) :
    ∀ z : Site 2, z ∈ qr.support → z ∈ ql.support → False := by
  intro z hzR hzL
  apply rlc_twoChannelFullPhysical_noGoodComponent_forbids_contactReachable
    hnoGood hxPath hyPath
  exact ⟨(qr.takeUntil z hzR).append (ql.takeUntil z hzL).reverse⟩


theorem
    rlc_twoChannelFullPhysical_noGood_prefixEndpoints_not_reachable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {x y ur ul : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul) :
    ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Reachable ur ul := by
  intro hru
  apply rlc_twoChannelFullPhysical_noGoodComponent_forbids_contactReachable
    hnoGood hxPath hyPath
  exact qr.reachable.trans (hru.trans ql.reachable.symm)


theorem rlc_twoChannelFullPhysical_reflectedLeftWalk_terminal_location
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
    (hxOriginal : rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∨
      rlc_dualReflect x ∈ rlc_pathVertices gamma'.1)
    (hleft : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (hloc :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect u) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect u)) :
    RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect u) := by
  rcases hloc with huLeft | huRight
  · exact huLeft
  · exfalso
    have hnotNil : ¬q.Nil := by
      intro hnil
      rcases hxOriginal with hxRight | hxLeft
      · exact huRight.2.2.1 (by simpa [hnil.eq] using hxRight)
      · exact huRight.2.2.2 (by simpa [hnil.eq] using hxLeft)
    have hlast := q.mk_penultimate_end_mem_edges hnotNil
    have hlastLeft : s(rlc_dualReflect q.penultimate,
        rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma'.1 := by
      simpa [Sym2.map_mk] using hleft s(q.penultimate, u) hlast
    have huLeft := rlc_reflectedPathEdge_endpoint_mem_vertices
      gamma'.1 hlastLeft (Sym2.mem_mk_right _ _)
    exact hfaith.reflectedTraceVertices_disjoint huRight.2.1 huLeft


theorem rlc_twoChannelFullPhysical_reflectedRightWalk_terminal_location
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x u : Site 2}
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
    (hxOriginal : rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∨
      rlc_dualReflect x ∈ rlc_pathVertices gamma'.1)
    (hright : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (hloc :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect u) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect u)) :
    RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
      gamma gamma' (rlc_dualReflect u) := by
  rcases hloc with huLeft | huRight
  · exfalso
    have hnotNil : ¬q.Nil := by
      intro hnil
      rcases hxOriginal with hxRight | hxLeft
      · exact huLeft.2.2.1 (by simpa [hnil.eq] using hxRight)
      · exact huLeft.2.2.2 (by simpa [hnil.eq] using hxLeft)
    have hlast := q.mk_penultimate_end_mem_edges hnotNil
    have hlastRight : s(rlc_dualReflect q.penultimate,
        rlc_dualReflect u) ∈ rlc_reflectedPathEdges gamma.1 := by
      simpa [Sym2.map_mk] using hright s(q.penultimate, u) hlast
    have huRight := rlc_reflectedPathEdge_endpoint_mem_vertices
      gamma.1 hlastRight (Sym2.mem_mk_right _ _)
    exact hfaith.reflectedTraceVertices_disjoint huRight huLeft.2.1
  · exact huRight


end
end StatMech.Universality
