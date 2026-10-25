/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part2
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

open FKMedialTurningFiber

noncomputable section

variable {T : EvenTorus}

def fkRectBlackOrbitList
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    List (FKMedialBlackDart T) :=
  (fkMedialBlackBoundaryPerm pairing).toList d

end
end StatMech.FrontierD
