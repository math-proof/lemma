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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part28
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipLiveBudget15.FieldwiseLe
    (B C : SourceClassEndpointMembershipLiveBudget15) : Prop :=
  B.zero_none ≤ C.zero_none ∧
    B.two_none ≤ C.two_none ∧
    B.two_endpoint ≤ C.two_endpoint ∧
    B.two_origin ≤ C.two_origin ∧
    B.two_ghost ≤ C.two_ghost ∧
    B.two_ghost_endpoint ≤ C.two_ghost_endpoint ∧
    B.two_ghost_origin ≤ C.two_ghost_origin ∧
    B.four_none ≤ C.four_none ∧
    B.four_endpoint ≤ C.four_endpoint ∧
    B.four_origin ≤ C.four_origin ∧
    B.four_origin_endpoint ≤ C.four_origin_endpoint ∧
    B.four_ghost ≤ C.four_ghost ∧
    B.four_ghost_endpoint ≤ C.four_ghost_endpoint ∧
    B.four_ghost_origin ≤ C.four_ghost_origin ∧
    B.four_ghost_origin_endpoint ≤ C.four_ghost_origin_endpoint

end Exact3D
end StatMech
