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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part35
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    Finset (Finset (Option (FK.boxVerts 3 n))) :=
  (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
    n Ω v).filter
    (fun S =>
      finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.fourPlus
            hasGhost hasOrigin hasEndpoint ∧
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
          k)

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) : ℝ :=
  ∑ S ∈
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
      n Ω v hasGhost hasOrigin hasEndpoint k,
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
      β H n Ω v S

end Exact3D
end StatMech
