/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part3
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

namespace FKMedialTurningFiber

def modeEquivCompatibleArrows (pairing : FKMedialLoopPairing T) :
    (FKMedialLoop T pairing → Bool) ≃
      {a : SixVertexArrows T //
        ∀ v, fkLoopPairingCompatible (pairing v) a v} where
  toFun mode := ⟨arrowsOfMode pairing mode,
    compatible_arrowsOfMode pairing mode⟩
  invFun a := modeOfArrows pairing a.1
  left_inv := modeOfArrows_arrowsOfMode pairing
  right_inv := by
    intro a
    apply Subtype.ext
    exact arrowsOfMode_modeOfArrows pairing a.1 a.2

noncomputable def componentTurn (pairing : FKMedialLoopPairing T)
    (a : SixVertexArrows T) (C : FKMedialLoop T pairing) : Int := by
  classical
  exact ∑ v : T.Vertex, (
    (if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .west) = C
      then turnSign (pairing v) (fkMedialDartIncoming a (v, .west)) else 0) +
    (if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .east) = C
      then turnSign (pairing v) (fkMedialDartIncoming a (v, .east)) else 0))

def canonicalComponentTurn (pairing : FKMedialLoopPairing T)
    (C : FKMedialLoop T pairing) : Int :=
  componentTurn pairing (arrowsOfMode pairing fun _ => false) C

end FKMedialTurningFiber
end
end StatMech.FrontierD
