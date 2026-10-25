/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterStraddle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWOuterOrientation.Part4
import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_outerExit_both_straddles_of_endpointSides
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcOuterExitEndpointSides G hn hlt omega) :
    rlc_TraceStraddlesLoop
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)) gamma.1 ∧
      rlc_TraceStraddlesLoop
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)) gamma'.1 := by
  exact ⟨rlc_traceStraddlesLoop_of_endpointSides _ gamma.1 h.1,
    rlc_traceStraddlesLoop_of_endpointSides _ gamma'.1 h.2⟩


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitEndpointSides
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hsides : RlcOuterExitEndpointSides G hn hlt omega)
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨hright, hleft⟩ :=
    rlc_outerExit_both_straddles_of_endpointSides G hn hlt omega hsides
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_outerExit_straddles
    G hn hlt omega hright hleft horder


end Universality
end StatMech
