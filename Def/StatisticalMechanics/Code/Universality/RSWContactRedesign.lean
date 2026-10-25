/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactRedesign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def RlcOuterExitTraceSeparation {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) : Prop :=
  let C := (rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
    (rlc_openSubgraph_le_lattice _)
  rlc_TraceStraddlesLoop C gamma.1 ∧
    rlc_TraceStraddlesLoop C gamma'.1


end Universality
end StatMech
