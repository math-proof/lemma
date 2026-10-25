/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part4
import Instance.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

def fkRectRefinedRawInteraction (v w : List (ons_Dart L)) : Int :=
  ∑ p : ZMod L × ZMod L,
    ((v.map (fun d => dartHorizontal d p)).sum *
        (w.map (fun d => dartVertical d (p.1, p.2 - 1))).sum -
      (v.map (fun d => dartVertical d p)).sum *
        (w.map (fun d => dartHorizontal d (p.1 - 1, p.2))).sum)

end
end StatMech.FrontierD
