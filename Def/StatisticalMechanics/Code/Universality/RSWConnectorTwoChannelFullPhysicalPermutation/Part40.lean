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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part39
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_twoChannelFullPhysical_cyclicOrderCrossingData_of_shiftedOuterTrace
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y z : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
    RlcTwoChannelFullPhysicalCyclicOrderCrossingData
      gamma gamma' omega := by
  have hn : 0 < n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hstrict := hfaith.right_axis_strict
    omega
  let trace := rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft
  apply rlc_twoChannelFullPhysical_cyclicOrderCrossingData_of_contactCycle
    hfaith c hx hy hxPath hyPath
      (-2 * n - 1) (2 * n) (-n - 1) n
      (traceStart := rlc_dualReflect.symm (gamma.1.2.1 : Site 2))
      (traceEnd := ![2 * n,
        (rlc_dualReflect.symm (gamma'.1.1 : Site 2)) 1])
      (trace := trace)
  · omega
  · omega
  · exact rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox
      hn gamma gamma' omega c hcycle hx
  · exact rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox
      hn gamma gamma' omega c hcycle hy
  · intro v hv
    exact rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox
      hn gamma gamma' omega c hcycle hv
  · exact rlc_bookShiftedOuterTrace_mem_faceBox
      gamma gamma' hzRight hzLeft trace.start_mem_support
  · exact rlc_bookShiftedOuterTrace_mem_faceBox
      gamma gamma' hzRight hzLeft trace.end_mem_support
  · exact rlc_bookShiftedOuterTrace_start_left gamma
  · simp
  · intro v hv
    exact rlc_bookShiftedOuterTrace_mem_faceBox
      gamma gamma' hzRight hzLeft hv


end
end StatMech.Universality
