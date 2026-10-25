/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWContactRedesign.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWReflectedRegion
import Def.StatisticalMechanics.Code.Universality.RSWTraceSeparation.Part3
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_tracePreimageWindingSplit_of_failure
    {n a b c d : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hJordan : RlcOuterExitJordanTraceSides G omega)
    (tau : RlcCrossingPath a b c d)
    (hsplit : RlcTracePreimagesSplit tau gamma gamma') :
    RlcTracePreimageRegionSplit tau
      (rlc_outerExitWindingRegion G omega) := by
  obtain ⟨x, hx, y, hy, hxy | hxy⟩ := hsplit
  · have hxK := rlc_rightPathVertex_mem_mixedWiredReachSet
      G omega hxy.1
    have hyK := rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno hxy.2
    exact ⟨x, hx, y, hy, Or.inl
      ⟨hJordan.1 hxK, hJordan.2 _ hxy.2 hyK⟩⟩
  · have hxK := rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno hxy.1
    have hyK := rlc_rightPathVertex_mem_mixedWiredReachSet
      G omega hxy.2
    exact ⟨x, hx, y, hy, Or.inr
      ⟨hJordan.2 _ hxy.1 hxK, hJordan.1 hyK⟩⟩


theorem rlc_outerExitJordanTraceSides_of_region_eq {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hregion : rlc_mixedWiredReachSet G omega =
      rlc_outerExitWindingRegion G omega) :
    RlcOuterExitJordanTraceSides G omega := by
  constructor
  · intro z hz
    rwa [← hregion]
  · intro z _hzPath hzK hzRegion
    exact hzK (hregion.symm ▸ hzRegion)


theorem rlc_outerExitTraceSeparation_of_failure_of_preimageSplit
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (htrace : RlcLowestHighestTracePreimageSplit gamma gamma')
    (hJordan : RlcOuterExitJordanTraceSides G omega) :
    RlcOuterExitTraceSeparation G hn hlt omega := by
  let C := (rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
    (rlc_openSubgraph_le_lattice _)
  have hregion : rlc_reflectedPrimalRegion
        (rlc_outerExitWindingRegion G omega) = jec_leftRegion C := by
    exact rlc_outerExit_reflectedRegion_eq_leftRegion_of_fill_eq
      G hn hlt omega (rlc_outerExitWindingRegion G omega) rfl
  have hright : RlcTracePreimageRegionSplit gamma.1
      (rlc_outerExitWindingRegion G omega) :=
    rlc_tracePreimageWindingSplit_of_failure
      G omega hno hJordan gamma.1 htrace.1
  have hleft : RlcTracePreimageRegionSplit gamma'.1
      (rlc_outerExitWindingRegion G omega) :=
    rlc_tracePreimageWindingSplit_of_failure
      G omega hno hJordan gamma'.1 htrace.2
  change rlc_TraceStraddlesLoop C gamma.1 ∧
    rlc_TraceStraddlesLoop C gamma'.1
  exact ⟨rlc_traceStraddlesLoop_of_preimageRegionSplit
      C gamma.1 _ hregion hright,
    rlc_traceStraddlesLoop_of_preimageRegionSplit
      C gamma'.1 _ hregion hleft⟩


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_failure_of_preimageSplit
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (htrace : RlcLowestHighestTracePreimageSplit gamma gamma')
    (hJordan : RlcOuterExitJordanTraceSides G omega)
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_traceSeparation
    G hn hlt omega
    (rlc_outerExitTraceSeparation_of_failure_of_preimageSplit
      G hn hlt omega hno htrace hJordan)
    horder

end Universality
end StatMech
