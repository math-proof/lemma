/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutFiberReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingPositiveBoundary.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEssentialClusterBoundary.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem sum_fkRectPrimalComponentBoundaryVerticalMass
    (R : FKRectTorus) (omega : R.Configuration) :
    ∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
        fkRectPrimalComponentBoundaryVerticalMass R omega K =
      ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        (fkRectBlackBoundaryCycleWinding R omega C).2.natAbs := by
  classical
  unfold fkRectPrimalComponentBoundaryVerticalMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.sum_eq_single
    (fkRectBlackBoundaryCyclePrimalComponent R omega C)]
  · simp
  · intro K _ hne
    simp [Ne.symm hne]
  · simp


theorem sum_fkRectPrimalComponentHorizontalCutCrossingCount
    (R : FKRectTorus) (omega : R.Configuration) :
    ∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
        fkRectPrimalComponentHorizontalCutCrossingCount R omega K =
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) := by
  classical
  let Crossing := {X : (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent //
    FKRectHorizontalCutPrimalCrossingComponent R
      (fkRectForceHorizontalCutClosed R omega) X}
  unfold fkRectPrimalComponentHorizontalCutCrossingCount
    fkRectHorizontalCutPrimalCrossingClusterCount
  change (∑ K : (fkRectOpenGraph R omega).ConnectedComponent,
      ((Finset.univ : Finset Crossing).filter fun X =>
        fkRectHorizontalCutComponentTorusComponent R omega X.1 = K).card) =
    Fintype.card Crossing
  simpa using (Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset Crossing)
    (Finset.univ : Finset
      (fkRectOpenGraph R omega).ConnectedComponent)
    (fun X : Crossing =>
      fkRectHorizontalCutComponentTorusComponent R omega X.1))


end
end StatMech.FrontierD
