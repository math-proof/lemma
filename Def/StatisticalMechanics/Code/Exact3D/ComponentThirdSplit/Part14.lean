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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part13
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointUnmarkedOptions
    {n : ℕ} (v : FK.boxVerts 3 n) :
    Finset (Option (FK.boxVerts 3 n)) :=
  (Finset.univ : Finset (Option (FK.boxVerts 3 n))).filter
    (fun x =>
      x ≠ none ∧
        x ≠ some (IsingFK.boxOrigin 3 n) ∧
        x ≠ some v)

end Exact3D
end StatMech
