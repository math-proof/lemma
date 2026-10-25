/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedSupportInteraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedSupportInteraction
open Finset


namespace StatMech.FrontierD

open IntegralSquareTorusCycle

def FKRectRefinedEdgeCenterNormal (horizontal : Bool)
    (c : Int × Int) : Prop :=
  if horizontal then
    ∃ x y : Int, c = (4 * x - 2, 4 * y)
  else
    ∃ x y : Int, c = (4 * x, 4 * y + 2)


end StatMech.FrontierD
