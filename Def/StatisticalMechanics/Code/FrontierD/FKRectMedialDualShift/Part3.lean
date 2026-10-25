/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part2


namespace StatMech.FrontierD

def fkRectMedialDualShiftGraphIso
    (R : FKRectTorus) (omega : R.Configuration) :
    fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega) ≃g
      fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega)) where
  toEquiv := fkRectMedialDualShiftDartEquiv R
  map_rel_iff' := by
    intro d e
    rw [fkMedialLoopGraph_adj_iff, fkMedialLoopGraph_adj_iff]
    constructor
    · rintro (hlocal | hbond)
      · left
        apply (fkRectMedialDualShiftDartEquiv R).injective
        change fkRectMedialDualShiftDart R e =
          fkRectMedialDualShiftDart R
            (fkMedialLocalMate
              (fkRectConfigurationToMedialPairing R omega) d)
        rw [fkRectMedialDualShiftDart_localMate]
        exact hlocal
      · right
        apply (fkRectMedialDualShiftDartEquiv R).injective
        change fkRectMedialDualShiftDart R e =
          fkRectMedialDualShiftDart R
            (fkMedialBondMate R.medialTorus d)
        rw [fkRectMedialDualShiftDart_bondMate]
        exact hbond
    · rintro (hlocal | hbond)
      · left
        change fkRectMedialDualShiftDart R e =
          fkMedialLocalMate
            (fkRectConfigurationToMedialPairing R
              (fkRectDualConfigurationEquiv R omega))
            (fkRectMedialDualShiftDart R d)
        rw [hlocal, fkRectMedialDualShiftDart_localMate]
      · right
        change fkRectMedialDualShiftDart R e =
          fkMedialBondMate R.medialTorus
            (fkRectMedialDualShiftDart R d)
        rw [hbond, fkRectMedialDualShiftDart_bondMate]

end StatMech.FrontierD
