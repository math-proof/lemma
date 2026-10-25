/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureSelectedCarryObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSourceArcPlacement.Part5
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def rlc_traceSplitCounterexample_failureAnchor : Sym2 (Site 2) :=
  s((![-1, -1] : Site 2), ![0, -1])

def rlc_failureSelectedCounterexampleRightSide (z : Site 2) : Prop :=
  z = ![-1, -2] ∨ z = ![-1, -1]

end Universality
end StatMech
