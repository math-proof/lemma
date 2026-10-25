/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWContactRedesign.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWReflectedRegion
import Def.StatisticalMechanics.Code.Universality.RSWTraceSeparation.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_outerExitTraceSeparation_iff_windingSplit
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    RlcOuterExitTraceSeparation G hn hlt omega ↔
      RlcOuterExitTraceWindingSplit G omega := by
  let C := (rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
    (rlc_openSubgraph_le_lattice _)
  have hregion : rlc_reflectedPrimalRegion
        (rlc_outerExitWindingRegion G omega) = jec_leftRegion C := by
    exact rlc_outerExit_reflectedRegion_eq_leftRegion_of_fill_eq
      G hn hlt omega (rlc_outerExitWindingRegion G omega) rfl
  change (rlc_TraceStraddlesLoop C gamma.1 ∧
      rlc_TraceStraddlesLoop C gamma'.1) ↔ _
  exact and_congr
    (rlc_traceStraddlesLoop_iff_preimageRegionSplit C gamma.1 _ hregion)
    (rlc_traceStraddlesLoop_iff_preimageRegionSplit C gamma'.1 _ hregion)


end Universality
end StatMech
