/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutUnits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingRankOneReduction
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutTouch.Part2
import Instance.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutUnits
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem card_fkRectHorizontalCutCrossingInFiber
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    Fintype.card (FKRectHorizontalCutCrossingInFiber R omega K) =
      fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
  classical
  rw [Fintype.card_subtype]
  rfl


theorem positiveBoundaryMass_le_crossingCount_iff_nonempty_embedding
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤
        fkRectPrimalComponentHorizontalCutCrossingCount R omega K ↔
      Nonempty (FKRectPositiveBoundaryUnit R omega K ↪
        FKRectHorizontalCutCrossingInFiber R omega K) := by
  rw [Function.Embedding.nonempty_iff_card_le,
    card_fkRectPositiveBoundaryUnit,
    card_fkRectHorizontalCutCrossingInFiber]


theorem rankOnePositiveBoundaryCutFiberBound_iff_unitEmbedding
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectRankOnePositiveVerticalBoundaryCutFiberBound R omega ↔
      ∀ K : (fkRectOpenGraph R omega).ConnectedComponent,
        ¬ FKRectPrimalComponentHasNet R omega K →
          Nonempty (FKRectPositiveBoundaryUnit R omega K ↪
            FKRectHorizontalCutCrossingInFiber R omega K) := by
  constructor
  · intro h K hnet
    rw [← positiveBoundaryMass_le_crossingCount_iff_nonempty_embedding]
    exact h K hnet
  · intro h K hnet
    rw [positiveBoundaryMass_le_crossingCount_iff_nonempty_embedding]
    exact h K hnet

end
end StatMech.FrontierD
