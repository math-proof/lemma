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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part15
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {x : Option (FK.boxVerts 3 n)} :
    x ∈
        finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ↔
      (x = none ∧ hasGhost = true) ∨
        (x = some (IsingFK.boxOrigin 3 n) ∧ hasOrigin = true) ∨
        (x = some v ∧ hasEndpoint = true) := by
  classical
  simp [finiteBoundaryGhostSourceClassEndpointMarkedSources]

end Exact3D
end StatMech
