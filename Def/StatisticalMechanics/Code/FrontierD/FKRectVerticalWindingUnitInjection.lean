/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingUnitInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingLevelPlateau.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryCompanionUnique
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingUnitInjection
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectMedialBoundaryPrimalTraceBetween
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) (a b : Nat) (hab : a ≤ b) :
    (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R
        ((fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))^[a] d))
      (fkRectMedialDartPrimalLabel R
        ((fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))^[b] d)) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let p := fkRectMedialBoundaryPrimalTrace R omega
    ((fkMedialBoundaryStep pairing)^[a] d) (b - a)
  have hend :
      (fkMedialBoundaryStep pairing)^[b - a]
          ((fkMedialBoundaryStep pairing)^[a] d) =
        (fkMedialBoundaryStep pairing)^[b] d := by
    rw [← Function.iterate_add_apply]
    congr 2
    omega
  exact p.copy rfl (congrArg (fkRectMedialDartPrimalLabel R) hend)


end
end StatMech.FrontierD
