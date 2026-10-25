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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part28
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure SourceClassEndpointMembershipLiveBudget15 where
  zero_none : ℝ
  two_none : ℝ
  two_endpoint : ℝ
  two_origin : ℝ
  two_ghost : ℝ
  two_ghost_endpoint : ℝ
  two_ghost_origin : ℝ
  four_none : ℝ
  four_endpoint : ℝ
  four_origin : ℝ
  four_origin_endpoint : ℝ
  four_ghost : ℝ
  four_ghost_endpoint : ℝ
  four_ghost_origin : ℝ
  four_ghost_origin_endpoint : ℝ

end Exact3D
end StatMech
