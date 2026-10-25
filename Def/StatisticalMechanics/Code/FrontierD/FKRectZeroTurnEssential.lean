/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnEssential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

open FKMedialTurningFiber StatMech.Onsager

noncomputable section

def fkRectBlackBoundaryPrimalCycleWalk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    (fkRectOpenGraph R omega).Walk
      (fkRectMedialDartPrimalLabel R d.1)
      (fkRectMedialDartPrimalLabel R d.1) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  let p := fkRectMedialBoundaryPrimalTrace R omega d.1 n
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d := by
    exact fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have hdart : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  exact p.copy rfl (congrArg (fkRectMedialDartPrimalLabel R) hdart)

end
end StatMech.FrontierD
