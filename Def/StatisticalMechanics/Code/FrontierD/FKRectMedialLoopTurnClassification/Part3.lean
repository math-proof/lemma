/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part3
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

open FKMedialTurningFiber

noncomputable section

variable {T : EvenTorus}

def fkRectBlackOrbitDirection
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (i : Fin (fkRectBlackOrbitList pairing d).length) : Fin 4 :=
  fkMedialStrandDirection pairing
    ((fkRectBlackOrbitList pairing d).get i).1

def fkRectBlackOrbitPrefix
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (n : Nat) : Int × Int :=
  ∑ k ∈ Finset.range n,
    stepOf (fkMedialStrandDirection pairing
      ((fkMedialBlackBoundaryPerm pairing)^[k] d).1)

end
end StatMech.FrontierD
