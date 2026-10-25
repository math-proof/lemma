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
import Structure.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part2
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipLiveBudget15.toBudget
    (B : SourceClassEndpointMembershipLiveBudget15)
    (c : SourceClassEndpointMembershipCase) : ℝ :=
  match c.cardCase, c.hasGhost, c.hasOrigin, c.hasEndpoint with
  | SourceClassCardinalityCase.zero, false, false, false =>
      B.zero_none
  | SourceClassCardinalityCase.two, false, false, false =>
      B.two_none
  | SourceClassCardinalityCase.two, false, false, true =>
      B.two_endpoint
  | SourceClassCardinalityCase.two, false, true, false =>
      B.two_origin
  | SourceClassCardinalityCase.two, true, false, false =>
      B.two_ghost
  | SourceClassCardinalityCase.two, true, false, true =>
      B.two_ghost_endpoint
  | SourceClassCardinalityCase.two, true, true, false =>
      B.two_ghost_origin
  | SourceClassCardinalityCase.fourPlus, false, false, false =>
      B.four_none
  | SourceClassCardinalityCase.fourPlus, false, false, true =>
      B.four_endpoint
  | SourceClassCardinalityCase.fourPlus, false, true, false =>
      B.four_origin
  | SourceClassCardinalityCase.fourPlus, false, true, true =>
      B.four_origin_endpoint
  | SourceClassCardinalityCase.fourPlus, true, false, false =>
      B.four_ghost
  | SourceClassCardinalityCase.fourPlus, true, false, true =>
      B.four_ghost_endpoint
  | SourceClassCardinalityCase.fourPlus, true, true, false =>
      B.four_ghost_origin
  | SourceClassCardinalityCase.fourPlus, true, true, true =>
      B.four_ghost_origin_endpoint
  | _, _, _, _ => 0

set_option linter.style.longLine false in


def SourceClassEndpointMembershipLiveBudget15.total
    (B : SourceClassEndpointMembershipLiveBudget15) : ℝ :=
  B.zero_none +
    B.two_none +
    B.two_endpoint +
    B.two_origin +
    B.two_ghost +
    B.two_ghost_endpoint +
    B.two_ghost_origin +
    B.four_none +
    B.four_endpoint +
    B.four_origin +
    B.four_origin_endpoint +
    B.four_ghost +
    B.four_ghost_endpoint +
    B.four_ghost_origin +
    B.four_ghost_origin_endpoint

end Exact3D
end StatMech
