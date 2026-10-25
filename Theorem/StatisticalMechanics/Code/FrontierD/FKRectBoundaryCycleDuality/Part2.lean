/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleDuality
open Equiv SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDualBlackDartEquiv_reachable_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (d e : FKMedialBlackDart R.medialTorus) :
    (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega))).Reachable
        ((fkRectDualBlackDartEquiv R omega d).1)
        ((fkRectDualBlackDartEquiv R omega e).1) ↔
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).Reachable d.1 e.1 := by
  let dualPairing := fkRectConfigurationToMedialPairing R
    (fkRectDualConfigurationEquiv R omega)
  change (fkMedialLoopGraph R.medialTorus dualPairing).Reachable
      (fkMedialLocalMate dualPairing
        (fkRectMedialDualShiftDart R d.1))
      (fkMedialLocalMate dualPairing
        (fkRectMedialDualShiftDart R e.1)) ↔ _
  constructor
  · intro h
    have hshift : (fkMedialLoopGraph R.medialTorus dualPairing).Reachable
        (fkRectMedialDualShiftDart R d.1)
        (fkRectMedialDualShiftDart R e.1) :=
      (fkMedial_reachable_localMate dualPairing _).trans
        (h.trans (fkMedial_reachable_localMate dualPairing _).symm)
    exact (fkRectMedialDualShiftGraphIso R omega).reachable_iff.mp hshift
  · intro h
    have hshift :=
      (fkRectMedialDualShiftGraphIso R omega).reachable_iff.mpr h
    exact (fkMedial_reachable_localMate dualPairing _).symm.trans
      (hshift.trans (fkMedial_reachable_localMate dualPairing _))


end
end StatMech.FrontierD
