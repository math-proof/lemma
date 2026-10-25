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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part87
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem liveSingletonOptionComponentBudgetScheduleSingleton_of_residualCaseShareBudget
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (h :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  ∃ share D : ℝ,
                    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
                      v β H Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n))) share D ∧
                    share * D ≤ budget.singletonBudget β H Ωnz v x) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical
      budget := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  dsimp only
  intro x hx
  rcases hn H hH Ω v hv x hx with ⟨share, D, hshare, hbudget⟩
  exact le_trans hshare.2 hbudget

set_option linter.style.longLine false in


theorem liveSingletonOptionComponentBudgetScheduleSingleton_of_namedResidualCaseShareBudget
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (h :
      LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical
        budget) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical
      budget :=
  liveSingletonOptionComponentBudgetScheduleSingleton_of_residualCaseShareBudget h

end Exact3D
end StatMech
