/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWReflectedRegion
import Theorem.StatisticalMechanics.Code.Universality.RSWShiftedEndpoint
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def RlcShiftedEndpointTraceSplit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  ((rlc_shiftedEndpointPreimage (gamma.1.1 : Site 2) ∈
        rlc_pathVertices gamma.1 ∧
      rlc_shiftedEndpointPreimage (gamma.1.2.1 : Site 2) ∈
        rlc_pathVertices gamma'.1) ∨
    (rlc_shiftedEndpointPreimage (gamma.1.1 : Site 2) ∈
        rlc_pathVertices gamma'.1 ∧
      rlc_shiftedEndpointPreimage (gamma.1.2.1 : Site 2) ∈
        rlc_pathVertices gamma.1)) ∧
  ((rlc_shiftedEndpointPreimage (gamma'.1.1 : Site 2) ∈
        rlc_pathVertices gamma.1 ∧
      rlc_shiftedEndpointPreimage (gamma'.1.2.1 : Site 2) ∈
        rlc_pathVertices gamma'.1) ∨
    (rlc_shiftedEndpointPreimage (gamma'.1.1 : Site 2) ∈
        rlc_pathVertices gamma'.1 ∧
      rlc_shiftedEndpointPreimage (gamma'.1.2.1 : Site 2) ∈
        rlc_pathVertices gamma.1))


end Universality
end StatMech
