/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Instance.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

namespace FKMedialTurningFiber

def turnSign (pairing incoming : Bool) : Int :=
  if pairing = incoming then 1 else -1

def vertexTurn (pairing : Bool) (a : SixVertexArrows T) (v : T.Vertex) : Int :=
  turnSign pairing (fkLoopWestIncoming a v) +
    turnSign pairing (fkLoopEastIncoming a v)

end FKMedialTurningFiber
end
end StatMech.FrontierD
