/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part6
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

def fkRectRefinedBoundaryOrbitTranslation {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T)
    (c : Int × Int) : Int × Int :=
  ((fkRectRefinedBoundaryCenterAfter pairing d c
      (orderOf (fkMedialBoundaryStep pairing))).1 - c.1,
    (fkRectRefinedBoundaryCenterAfter pairing d c
      (orderOf (fkMedialBoundaryStep pairing))).2 - c.2)


end
end StatMech.FrontierD
