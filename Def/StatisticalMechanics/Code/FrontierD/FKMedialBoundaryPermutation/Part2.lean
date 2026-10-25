/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation
open SimpleGraph Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


def fkMedialBlackBoundaryPerm (pairing : FKMedialLoopPairing T) :
    Perm (FKMedialBlackDart T) :=
  (fkMedialBoundaryStep pairing).subtypePerm fun d => by
    rw [fkMedialCheckerColor_boundaryStep]

end StatMech.FrontierD
