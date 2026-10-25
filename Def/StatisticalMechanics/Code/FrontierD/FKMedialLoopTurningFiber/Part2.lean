/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

namespace FKMedialTurningFiber

def modeIncoming (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) (d : FKMedialDart T) : Bool :=
  if mode ((fkMedialLoopGraph T pairing).connectedComponentMk d) then
    !fkMedialCheckerColor d
  else fkMedialCheckerColor d

def arrowsOfMode (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) : SixVertexArrows T where
  horizontal v := !modeIncoming pairing mode (v, .east)
  vertical v := !modeIncoming pairing mode (v, .north)

end FKMedialTurningFiber
end
end StatMech.FrontierD
