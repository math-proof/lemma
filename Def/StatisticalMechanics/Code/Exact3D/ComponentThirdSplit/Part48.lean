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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part45
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    SourceClassEndpointMembershipLiveBudget15 :=
  finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15
    β H n Ω v
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
      β H n Ω v false false false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
      β H n Ω v false false true)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
      β H n Ω v false true false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
      β H n Ω v false true true)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
      β H n Ω v true false false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
      β H n Ω v true false true)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
      β H n Ω v true true false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
      β H n Ω v true true true)

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    SourceClassEndpointMembershipLiveBudget15 :=
  finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15
    β H n Ω v
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
      β H n Ω v false false false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
      β H n Ω v false false true)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
      β H n Ω v false true false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
      β H n Ω v false true true)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
      β H n Ω v true false false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
      β H n Ω v true false true)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
      β H n Ω v true true false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
      β H n Ω v true true true)

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    SourceClassEndpointMembershipLiveBudget15 :=
  finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15
    β H n Ω v
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
      β H n Ω v false false false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
      β H n Ω v false false true)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
      β H n Ω v false true false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
      β H n Ω v false true true)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
      β H n Ω v true false false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
      β H n Ω v true false true)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
      β H n Ω v true true false)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
      β H n Ω v true true true)

end Exact3D
end StatMech
