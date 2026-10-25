/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation
open SimpleGraph Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


@[simp] theorem fkMedialBoundaryStep_apply
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    fkMedialBoundaryStep pairing d =
      fkMedialBondMate T (fkMedialLocalMate pairing d) := rfl


theorem fkMedialCheckerColor_boundaryStep
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    fkMedialCheckerColor (fkMedialBoundaryStep pairing d) =
      fkMedialCheckerColor d := by
  have hlocal := fkMedialCheckerColor_localMate_ne pairing d
  have hbond := fkMedialCheckerColor_bondMate_ne T
    (fkMedialLocalMate pairing d)
  simp only [fkMedialBoundaryStep_apply] at hbond ⊢
  generalize hd : fkMedialCheckerColor d = bd at hlocal ⊢
  generalize hl : fkMedialCheckerColor
    (fkMedialLocalMate pairing d) = bl at hlocal hbond
  generalize hb : fkMedialCheckerColor
    (fkMedialBondMate T (fkMedialLocalMate pairing d)) = bb at hbond ⊢
  cases bd <;> cases bl <;> cases bb <;> simp_all


end StatMech.FrontierD
