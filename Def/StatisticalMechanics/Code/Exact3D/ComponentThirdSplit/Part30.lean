/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part27
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

def SourceClassEndpointMembershipLiveBudget15.Nonneg
    (B : SourceClassEndpointMembershipLiveBudget15) : Prop :=
  0 ≤ B.zero_none ∧
    0 ≤ B.two_none ∧
    0 ≤ B.two_endpoint ∧
    0 ≤ B.two_origin ∧
    0 ≤ B.two_ghost ∧
    0 ≤ B.two_ghost_endpoint ∧
    0 ≤ B.two_ghost_origin ∧
    0 ≤ B.four_none ∧
    0 ≤ B.four_endpoint ∧
    0 ≤ B.four_origin ∧
    0 ≤ B.four_origin_endpoint ∧
    0 ≤ B.four_ghost ∧
    0 ≤ B.four_ghost_endpoint ∧
    0 ≤ B.four_ghost_origin ∧
    0 ≤ B.four_ghost_origin_endpoint

end Exact3D
end StatMech
