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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part51
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_rightArcBadLocation_of_not_exclusive
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} {z : Site 2}
    (hbad : RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z)
    (hnot : ¬(RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' z ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' z)) :
    z ∈ rlc_pathVertices gamma.1 ∨
      z 0 = -2 * n ∨ z 0 = 2 * n ∨ z 1 = -n ∨ z 1 = n := by
  rcases hbad with hright | hleft | hrightReflected | hwall
  · exact Or.inl hright
  · exact False.elim (hnot (Or.inl hleft))
  · exact False.elim (hnot (Or.inr hrightReflected))
  · exact Or.inr hwall


theorem rlc_leftArcTargetBadLocation_of_not_exclusive
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} {z : Site 2}
    (hbad : RlcTwoChannelFullPhysicalLeftArcTargetBadLocation gamma gamma' z)
    (hnot : ¬(RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' z ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' z)) :
    z ∈ rlc_pathVertices gamma'.1 ∨
      z 0 = -2 * n ∨ z 0 = 2 * n ∨ z 1 = -n ∨ z 1 = n := by
  rcases hbad with hleft | hleftReflected | hrightReflected | hwall
  · exact Or.inl hleft
  · exact False.elim (hnot (Or.inl hleftReflected))
  · exact False.elim (hnot (Or.inr hrightReflected))
  · exact Or.inr hwall


theorem rlc_rightArcClassifiedBad_of_terminal_not_exclusive
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u v : Site 2}
    (hclass : RlcTwoChannelFullPhysicalRightArcClassifiedBad
      gamma gamma' omega u v)
    (hnot : ¬(RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect u) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect u))) :
    ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧
      (rlc_dualReflect u ∈ rlc_pathVertices gamma.1 ∨
        (rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n)) ∨
      ∃ p q : Site 2,
        sharedPrimalEdge u v = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
          RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p := by
  rcases hclass with ⟨hbad, hloc⟩ | hsource
  · exact Or.inl ⟨hbad,
      rlc_rightArcBadLocation_of_not_exclusive hloc hnot⟩
  · exact Or.inr hsource


theorem rlc_leftArcClassifiedBad_of_terminal_not_exclusive
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u v : Site 2}
    (hclass : RlcTwoChannelFullPhysicalLeftArcClassifiedBad
      gamma gamma' omega u v)
    (hnot : ¬(RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect u) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect u))) :
    ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧
      (rlc_dualReflect u ∈ rlc_pathVertices gamma'.1 ∨
        (rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n)) ∨
      ∃ p q : Site 2,
        sharedPrimalEdge u v = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
          RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p := by
  rcases hclass with ⟨hbad, hloc⟩ | hsource
  · exact Or.inl ⟨hbad,
      rlc_leftArcTargetBadLocation_of_not_exclusive hloc hnot⟩
  · exact Or.inr hsource


end
end StatMech.Universality
