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
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurnWalk
open Equiv


namespace StatMech.FrontierD

open StatMech.Onsager

open FKMedialTurningFiber

variable {T : EvenTorus}

noncomputable def blackComponentTurn
    (pairing : FKMedialLoopPairing T) (C : FKMedialLoop T pairing) : Int := by
  classical
  exact ∑ d : FKMedialBlackDart T,
    if (fkMedialLoopGraph T pairing).connectedComponentMk d.1 = C then
      turnSign (pairing d.1.1) (fkMedialVertexParity d.1.1)
    else 0

end StatMech.FrontierD
