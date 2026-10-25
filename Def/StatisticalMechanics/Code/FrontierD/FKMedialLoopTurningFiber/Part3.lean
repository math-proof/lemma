/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part2
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

namespace FKMedialTurningFiber

def modeOfArrows (pairing : FKMedialLoopPairing T)
    (a : SixVertexArrows T) (C : FKMedialLoop T pairing) : Bool :=
  fkMedialDartIncoming a C.out ^^ fkMedialCheckerColor C.out

end FKMedialTurningFiber
end
end StatMech.FrontierD
