/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWContactRedesign.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWReflectedRegion
import Def.StatisticalMechanics.Code.Universality.RSWTraceSeparation
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_tracePreimageRegionSplit_of_failure
    {n a b c d : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (tau : RlcCrossingPath a b c d)
    (hsplit : RlcTracePreimagesSplit tau gamma gamma') :
    RlcTracePreimageRegionSplit tau (rlc_mixedWiredReachSet G omega) := by
  obtain ⟨x, hx, y, hy, hxy | hxy⟩ := hsplit
  · exact ⟨x, hx, y, hy, Or.inl
      ⟨rlc_rightPathVertex_mem_mixedWiredReachSet G omega hxy.1,
        rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
          G omega hno hxy.2⟩⟩
  · exact ⟨x, hx, y, hy, Or.inr
      ⟨rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
          G omega hno hxy.1,
        rlc_rightPathVertex_mem_mixedWiredReachSet G omega hxy.2⟩⟩


theorem rlc_traceStraddlesLoop_of_preimageRegionSplit
    {a b c d : ℤ} {u : Site 2}
    (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d) (K : Set (Site 2))
    (hregion : rlc_reflectedPrimalRegion K = jec_leftRegion C)
    (hsplit : RlcTracePreimageRegionSplit gamma K) :
    rlc_TraceStraddlesLoop C gamma := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hsplit
  refine ⟨x, hx, y, hy, ?_⟩
  rw [rlc_oppositeLoopSides_iff_leftRegion_xor, ← hregion]
  simpa only [rlc_mem_reflectedPrimalRegion_iff] using hxy


theorem rlc_traceStraddlesLoop_iff_preimageRegionSplit
    {a b c d : ℤ} {u : Site 2}
    (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d) (K : Set (Site 2))
    (hregion : rlc_reflectedPrimalRegion K = jec_leftRegion C) :
    rlc_TraceStraddlesLoop C gamma ↔
      RlcTracePreimageRegionSplit gamma K := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨x, hx, y, hy, ?_⟩
    rw [rlc_oppositeLoopSides_iff_leftRegion_xor, ← hregion] at hxy
    simpa only [rlc_mem_reflectedPrimalRegion_iff] using hxy
  · exact rlc_traceStraddlesLoop_of_preimageRegionSplit
      C gamma K hregion


end Universality
end StatMech
