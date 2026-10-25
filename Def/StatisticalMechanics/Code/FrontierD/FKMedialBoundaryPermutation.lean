/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
open SimpleGraph Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


def fkMedialLocalMateEquiv (pairing : FKMedialLoopPairing T) :
    FKMedialDart T ≃ FKMedialDart T where
  toFun := fkMedialLocalMate pairing
  invFun := fkMedialLocalMate pairing
  left_inv := fkMedialLocalMate_involutive pairing
  right_inv := fkMedialLocalMate_involutive pairing


def fkMedialBondMateEquiv (T : EvenTorus) :
    FKMedialDart T ≃ FKMedialDart T where
  toFun := fkMedialBondMate T
  invFun := fkMedialBondMate T
  left_inv := fkMedialBondMate_involutive T
  right_inv := fkMedialBondMate_involutive T


def fkMedialBoundaryStep (pairing : FKMedialLoopPairing T) :
    Perm (FKMedialDart T) :=
  (fkMedialLocalMateEquiv pairing).trans (fkMedialBondMateEquiv T)

end StatMech.FrontierD
