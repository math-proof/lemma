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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part68
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcTwoChannelFullPhysicalWallTerminalProductClassification
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y ur vr ul vl : Site 2}
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul) : Prop where
  rightPrefix :
    (∀ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ∨
      ∃ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∉
          rlc_connectorFourTraceEdges gamma gamma'
  leftPrefix :
    (∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ∨
      ∃ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∉
          rlc_connectorFourTraceEdges gamma gamma'
  rightTerminal :
    (RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' (rlc_dualReflect ur) ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' (rlc_dualReflect ur)) ∨
    (¬(RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect ur) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect ur)) ∧
      RlcTwoChannelFullPhysicalRightArcNonExclusiveLocalizedBad
        gamma gamma' omega ur vr)
  leftTerminal :
    (RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' (rlc_dualReflect ul) ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' (rlc_dualReflect ul)) ∨
    (¬(RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect ul) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect ul)) ∧
      RlcTwoChannelFullPhysicalLeftArcNonExclusiveLocalizedBad
        gamma gamma' omega ul vl)
  terminalTable :
    (∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma') →
    (∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma') →
    (RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' (rlc_dualReflect ur) ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' (rlc_dualReflect ur)) →
    (RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' (rlc_dualReflect ul) ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' (rlc_dualReflect ul)) →
    RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable
      gamma gamma' omega qr ql


end
end StatMech.Universality
