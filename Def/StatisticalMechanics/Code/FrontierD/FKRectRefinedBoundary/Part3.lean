/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectRefinedBoundaryCenterAfter {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) :
    FKMedialDart T → (Int × Int) → Nat → (Int × Int)
  | _, c, 0 => c
  | d, c, n + 1 =>
      fkRectRefinedBoundaryCenterAfter pairing
        (fkMedialBoundaryStep pairing d)
        (fkRectRefinedBondCenter c
          (fkMedialLocalMate pairing d).2) n


def fkRectRefinedBoundaryDarts {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) :
    FKMedialDart T → (Int × Int) → Nat →
      List FKRectIntegralSquareDart
  | _, _, 0 => []
  | d, c, n + 1 =>
      fkRectRefinedLocalDarts (pairing d.1) c d.2 ++
        fkRectRefinedBoundaryDarts pairing
          (fkMedialBoundaryStep pairing d)
          (fkRectRefinedBondCenter c
            (fkMedialLocalMate pairing d).2) n


end
end StatMech.FrontierD
