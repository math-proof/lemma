/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWRayTransport.Part4
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def RlcReflectedEndpointXor {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (K : Set (Site 2)) : Prop :=
  (((gamma.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K) ≠
      ((gamma.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K)) ∧
    (((gamma'.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K) ≠
      ((gamma'.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K))


end Universality
end StatMech
