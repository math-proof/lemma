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
import Structure.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_twoChannelFullPhysical_cyclicOrderCrossingData_of_contactCycle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (alpha beta bottom top : Int)
    (hab : alpha < beta) (hbt : bottom ≤ top)
    (hxBox : x ∈ rect alpha beta bottom top)
    (hyBox : y ∈ rect alpha beta bottom top)
    (hcBox : ∀ z ∈ c.support, z ∈ rect alpha beta bottom top)
    (traceStart traceEnd : Site 2)
    (trace : (hypercubicLattice 2).Walk traceStart traceEnd)
    (hstartBox : traceStart ∈ rect alpha beta bottom top)
    (hendBox : traceEnd ∈ rect alpha beta bottom top)
    (hstart : traceStart 0 = alpha) (hend : traceEnd 0 = beta)
    (htraceBox : ∀ z ∈ trace.support,
      z ∈ rect alpha beta bottom top) :
    RlcTwoChannelFullPhysicalCyclicOrderCrossingData
      gamma gamma' omega := by
  let arc := rlc_orderedContourArc c hx hy
  have harcBox : ∀ z ∈ arc.support,
      z ∈ rect alpha beta bottom top := by
    intro z hz
    apply hcBox z
    have hzRotate : z ∈ (c.rotate x hx).support :=
      (c.rotate x hx).support_takeUntil_subset_support
        ((SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy) hz
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).1 hzRotate
  exact {
    x := x
    y := y
    right_contact := hxPath
    left_contact := hyPath
    right_contact_position := hfaith.dualFace_rightContact_position hxPath
    left_contact_position := hfaith.dualFace_leftContact_position hyPath
    arc := arc
    alpha := alpha
    beta := beta
    bottom := bottom
    top := top
    alpha_lt_beta := hab
    bottom_le_top := hbt
    x_mem_box := hxBox
    y_mem_box := hyBox
    arc_mem_box := harcBox
    traceStart := traceStart
    traceEnd := traceEnd
    trace := trace
    traceStart_mem_box := hstartBox
    traceEnd_mem_box := hendBox
    traceStart_left := hstart
    traceEnd_right := hend
    trace_mem_box := htraceBox }


def RlcTwoChannelFullPhysicalCyclicOrderCrossingData.toCertificate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (D : RlcTwoChannelFullPhysicalCyclicOrderCrossingData
      gamma gamma' omega)
    (hpre : ∀ z ∈ D.trace.support,
      z ∈ (sw_vertSeg (D.x 0) D.bottom (D.x 1)).support →
        z ∈ D.arc.support)
    (hpost : ∀ z ∈ D.trace.support,
      z ∈ (sw_vertSeg (D.y 0) (D.y 1) D.top).support →
        z ∈ D.arc.support)
    (hdisjoint : ∀ z ∈ D.trace.support, z ∉ D.arc.support) :
    RlcTwoChannelFullPhysicalCyclicOrderCrossingCertificate
      gamma gamma' omega where
  toRlcTwoChannelFullPhysicalCyclicOrderCrossingData := D
  lower_collar_contact := hpre
  upper_collar_contact := hpost
  trace_disjoint_arc := hdisjoint


end
end StatMech.Universality
