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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part36
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcTwoChannelFullPhysicalCyclicOrderCrossingData
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') where
  x : Site 2
  y : Site 2
  right_contact : rlc_dualReflect x ∈ rlc_pathVertices gamma.1
  left_contact : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1
  right_contact_position : (x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1
  left_contact_position : (y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0
  arc : (faceBoundaryGraph
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y
  alpha : Int
  beta : Int
  bottom : Int
  top : Int
  alpha_lt_beta : alpha < beta
  bottom_le_top : bottom ≤ top
  x_mem_box : x ∈ rect alpha beta bottom top
  y_mem_box : y ∈ rect alpha beta bottom top
  arc_mem_box : ∀ z ∈ arc.support, z ∈ rect alpha beta bottom top
  traceStart : Site 2
  traceEnd : Site 2
  trace : (hypercubicLattice 2).Walk traceStart traceEnd
  traceStart_mem_box : traceStart ∈ rect alpha beta bottom top
  traceEnd_mem_box : traceEnd ∈ rect alpha beta bottom top
  traceStart_left : traceStart 0 = alpha
  traceEnd_right : traceEnd 0 = beta
  trace_mem_box : ∀ z ∈ trace.support,
    z ∈ rect alpha beta bottom top


structure RlcTwoChannelFullPhysicalCyclicOrderCrossingCertificate
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    extends RlcTwoChannelFullPhysicalCyclicOrderCrossingData
      gamma gamma' omega where
  lower_collar_contact : ∀ z ∈ trace.support,
    z ∈ (sw_vertSeg (x 0) bottom (x 1)).support → z ∈ arc.support
  upper_collar_contact : ∀ z ∈ trace.support,
    z ∈ (sw_vertSeg (y 0) (y 1) top).support → z ∈ arc.support
  trace_disjoint_arc : ∀ z ∈ trace.support, z ∉ arc.support


end
end StatMech.Universality
