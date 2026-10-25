/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

def fkRectRefinedPrimalCenterlineDarts (pairing : Bool) (c : Int × Int) :
    List FKRectIntegralSquareDart :=
  if pairing then
    [((c.1 + 2, c.2), 2), ((c.1 + 1, c.2), 2), ((c.1, c.2), 2),
      ((c.1 - 1, c.2), 2)]
  else
    [((c.1, c.2 - 2), 1), ((c.1, c.2 - 1), 1), ((c.1, c.2), 1),
      ((c.1, c.2 + 1), 1)]


end
end StatMech.FrontierD
