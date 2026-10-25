/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWFailureSelectedCarryObstruction
import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def RlcFailureSelectedExtremalTraceTopology {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') : Prop :=
  ∀ (omega : ConfigSpace (Sym2 (Site 2))),
    omega ∉ rlc_mixedWiredConnectorEvent G →
      Nonempty (RlcRetainedFailureAnchoredContour G omega)


end Universality
end StatMech
