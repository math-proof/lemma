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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectBlackBoundaryCyclePrimalComponent
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectConfigurationBlackBoundaryCycle R omega →
      (fkRectOpenGraph R omega).ConnectedComponent := by
  classical
  apply Quot.lift (fun d : FKMedialBlackDart R.medialTorus =>
    (fkRectOpenGraph R omega).connectedComponentMk
      (fkRectMedialDartPrimalLabel R d.1))
  intro d e hde
  apply ConnectedComponent.sound
  have hmedial :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).Reachable d.1 e.1 :=
    (fkMedial_blackBoundary_sameCycle_iff_reachable
      (fkRectConfigurationToMedialPairing R omega) d e).mp hde
  exact fkRectMedial_reachable_primalLabel_reachable R omega hmedial

end
end StatMech.FrontierD
