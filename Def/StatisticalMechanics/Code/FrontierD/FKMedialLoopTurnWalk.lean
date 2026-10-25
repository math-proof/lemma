/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurnWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
open Equiv


namespace StatMech.FrontierD

open StatMech.Onsager

open FKMedialTurningFiber

variable {T : EvenTorus}

def fkMedialStrandDirection (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) : Fin 4 :=
  match pairing d.1, d.2 with
  | false, .west | false, .south => 0
  | false, .east | false, .north => 2
  | true, .west | true, .north => 1
  | true, .east | true, .south => 3

end StatMech.FrontierD
