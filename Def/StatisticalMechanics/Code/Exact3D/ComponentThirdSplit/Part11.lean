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
import Structure.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase :
    SourceClassEndpointMembershipCase where
  cardCase := SourceClassCardinalityCase.zero
  hasGhost := false
  hasOrigin := false
  hasEndpoint := false

set_option linter.style.longLine false in


def finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointNoGhostCase :
    SourceClassEndpointMembershipCase where
  cardCase := SourceClassCardinalityCase.two
  hasGhost := false
  hasOrigin := true
  hasEndpoint := true

set_option linter.style.longLine false in


def finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointGhostCase :
    SourceClassEndpointMembershipCase where
  cardCase := SourceClassCardinalityCase.two
  hasGhost := true
  hasOrigin := true
  hasEndpoint := true

set_option linter.style.longLine false in


def finiteBoundaryGhostSourceClassEndpointMembershipCase
    {n : ℕ}
    (v : FK.boxVerts 3 n)
    (S : Finset (Option (FK.boxVerts 3 n))) :
    SourceClassEndpointMembershipCase where
  cardCase := finiteBoundaryGhostSourceClassCardinalityCase S
  hasGhost := decide (none ∈ S)
  hasOrigin := decide (some (IsingFK.boxOrigin 3 n) ∈ S)
  hasEndpoint := decide (some v ∈ S)

end Exact3D
end StatMech
