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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part24
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_noGoodComponent_forbids_contactReachable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {x y : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Reachable x y := by
  intro hxy
  exact hnoGood ⟨x, y, hxy, hxPath, hyPath⟩

theorem rlc_twoChannelFullPhysical_noGood_rightWalk_end_not_leftContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {x u : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u) :
    rlc_dualReflect u ∉ rlc_pathVertices gamma'.1 := by
  intro huPath
  exact (rlc_twoChannelFullPhysical_noGoodComponent_forbids_contactReachable
    hnoGood hxPath huPath) q.reachable

theorem rlc_twoChannelFullPhysical_noGood_leftWalk_end_not_rightContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {y u : Site 2}
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y u) :
    rlc_dualReflect u ∉ rlc_pathVertices gamma.1 := by
  intro huPath
  exact (rlc_twoChannelFullPhysical_noGoodComponent_forbids_contactReachable
    hnoGood huPath hyPath) q.reachable.symm


end
end StatMech.Universality
