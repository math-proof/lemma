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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part16
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset :
    Finset SourceClassEndpointMembershipCase :=
  {
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.zero false false false,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.two false false false,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.two false false true,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.two false true false,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.two true false false,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.two true false true,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.two true true false,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.fourPlus false false false,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.fourPlus false false true,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.fourPlus false true false,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.fourPlus false true true,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.fourPlus true false false,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.fourPlus true false true,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.fourPlus true true false,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.fourPlus true true true
  }

end Exact3D
end StatMech
