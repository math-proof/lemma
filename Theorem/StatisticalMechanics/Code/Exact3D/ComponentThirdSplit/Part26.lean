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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part26
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_dependentCoefficientLabelComponentSum
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι n}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientDependentLabelComponentSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let denom :=
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with
    ⟨coefficientBudget, hcase, htotal⟩
  have hcoeff :
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
        ∑ i, coefficientBudget i :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_le_of_label_sum_le
      β H n Ωnz v (label Ωnz v) hcase le_rfl
  let base :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  have htotal' : base + (∑ i, coefficientBudget i) ≤ denom := by
    simpa [base, cap, denom, Ωnz] using htotal
  calc
    cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v =
        base +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v := by
      ring
    _ ≤ base + ∑ i, coefficientBudget i :=
      add_le_add le_rfl hcoeff
    _ ≤ denom := htotal'

end Exact3D
end StatMech
