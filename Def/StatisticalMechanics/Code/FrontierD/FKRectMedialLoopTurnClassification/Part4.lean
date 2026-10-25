/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part4
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

open FKMedialTurningFiber

noncomputable section

variable {T : EvenTorus}

def fkRectBlackDeckPointShift (R : FKRectTorus) (u : Int × Int) :
    Int × Int :=
  (4 * (fkRectSquareDeckTranslation R u).1,
    4 * (fkRectSquareDeckTranslation R u).2)

end
end StatMech.FrontierD
