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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part8
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {n : ℕ} {v : FK.boxVerts 3 n}
    (D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v) :
    0 ≤ finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D := by
  unfold finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
  exact
    mul_nonneg (Nat.cast_nonneg _)
      (finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight_nonneg
        hβ hH D)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_support_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      ∑ D ∈
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
            n Ω v,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D := by
  rfl

end Exact3D
end StatMech
