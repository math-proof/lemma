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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part36
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
    {n : ℕ} (v : FK.boxVerts 3 n) (k : ℕ) :
    Finset (Finset (Option (FK.boxVerts 3 n))) :=
  (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
    (fun R => R.card = k)

end Exact3D
end StatMech
