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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part57
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y ur ul : Site 2}
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul) : Prop :=
  ((∀ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' (rlc_dualReflect ur) ∧
      (∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' (rlc_dualReflect ul)) ∨
    ((∀ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' (rlc_dualReflect ur) ∧
      (∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' (rlc_dualReflect ul)) ∨
    ((∀ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' (rlc_dualReflect ur) ∧
      (∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' (rlc_dualReflect ul)) ∨
    ((∀ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' (rlc_dualReflect ur) ∧
      (∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' (rlc_dualReflect ul))


end
end StatMech.Universality
