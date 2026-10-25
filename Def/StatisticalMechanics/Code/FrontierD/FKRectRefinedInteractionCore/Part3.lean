/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part3
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

def fkRectRefinedPointTranslate (u p : ZMod L × ZMod L) :
    ZMod L × ZMod L :=
  (p.1 + u.1, p.2 + u.2)


def fkRectRefinedDartTranslateMod (u : ZMod L × ZMod L)
    (d : ons_Dart L) : ons_Dart L :=
  (fkRectRefinedPointTranslate u d.1, d.2)

end
end StatMech.FrontierD
