/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitVisits.Part2
open scoped BigOperators
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

def permOrbitSignedVisitTrace {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha] (sigma : Perm alpha) (d a b : alpha) : Nat -> Int
  | 0 => 0
  | n + 1 =>
      (if d = a then 1 else 0) - (if d = b then 1 else 0) +
        permOrbitSignedVisitTrace sigma (sigma d) a b n

end
end StatMech.FrontierD
