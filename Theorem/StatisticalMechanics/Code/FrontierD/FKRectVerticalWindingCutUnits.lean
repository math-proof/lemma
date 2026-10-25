/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutUnits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingRankOneReduction
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutTouch.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutUnits
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem card_fkRectPositiveBoundaryUnit
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    Fintype.card (FKRectPositiveBoundaryUnit R omega K) =
      fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  unfold fkRectPositiveBoundaryUnitMultiplicity
    fkRectPrimalComponentPositiveBoundaryVerticalMass
  apply Finset.sum_congr rfl
  intro C _
  rfl

theorem FKRectPositiveBoundaryUnit.component
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (u : FKRectPositiveBoundaryUnit R omega K) :
    fkRectBlackBoundaryCyclePrimalComponent R omega u.1 = K := by
  have hu := u.2.isLt
  unfold fkRectPositiveBoundaryUnitMultiplicity at hu
  split at hu <;> simp_all

theorem FKRectPositiveBoundaryUnit.winding_snd_pos
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent)
    (u : FKRectPositiveBoundaryUnit R omega K) :
    0 < (fkRectBlackBoundaryCycleWinding R omega u.1).2 := by
  have hu := u.2.isLt
  unfold fkRectPositiveBoundaryUnitMultiplicity at hu
  split at hu
  · omega
  · simp at hu


end
end StatMech.FrontierD
