/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part3
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

namespace FKMedialTurningFiber

theorem modeIncoming_modeOfArrows
    (pairing : FKMedialLoopPairing T) (a : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v)
    (d : FKMedialDart T) :
    modeIncoming pairing (modeOfArrows pairing a) d =
      fkMedialDartIncoming a d := by
  let C := (fkMedialLoopGraph T pairing).connectedComponentMk d
  have hreach : (fkMedialLoopGraph T pairing).Reachable C.out d :=
    SimpleGraph.ConnectedComponent.exact C.out_eq
  have hiff := incoming_eq_color_iff_reachable pairing a hcompat hreach
  unfold modeIncoming modeOfArrows
  change (if fkMedialDartIncoming a C.out ^^ fkMedialCheckerColor C.out
      then !fkMedialCheckerColor d else fkMedialCheckerColor d) = _
  generalize ho : fkMedialDartIncoming a C.out = o at hiff ⊢
  generalize hco : fkMedialCheckerColor C.out = co at hiff ⊢
  generalize hd : fkMedialDartIncoming a d = x at hiff ⊢
  generalize hcd : fkMedialCheckerColor d = cd at hiff ⊢
  cases o <;> cases co <;> cases x <;> cases cd <;> simp_all

theorem arrowsOfMode_modeOfArrows
    (pairing : FKMedialLoopPairing T) (a : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v) :
    arrowsOfMode pairing (modeOfArrows pairing a) = a := by
  ext v
  · have h := modeIncoming_modeOfArrows pairing a hcompat (v, .east)
    change (!modeIncoming pairing (modeOfArrows pairing a) (v, .east)) =
      a.horizontal v
    rw [h]
    simp [fkMedialDartIncoming, fkLoopEastIncoming]
  · have h := modeIncoming_modeOfArrows pairing a hcompat (v, .north)
    change (!modeIncoming pairing (modeOfArrows pairing a) (v, .north)) =
      a.vertical v
    rw [h]
    simp [fkMedialDartIncoming, fkLoopNorthIncoming]

theorem modeOfArrows_arrowsOfMode
    (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) :
    modeOfArrows pairing (arrowsOfMode pairing mode) = mode := by
  funext C
  unfold modeOfArrows
  rw [incoming_arrowsOfMode]
  unfold modeIncoming
  have hm : mode ((fkMedialLoopGraph T pairing).connectedComponentMk C.out) =
      mode C := congrArg mode C.out_eq
  rw [hm]
  change ((if mode C then !fkMedialCheckerColor C.out
    else fkMedialCheckerColor C.out) ^^ fkMedialCheckerColor C.out) = mode C
  cases mode C <;> cases fkMedialCheckerColor C.out <;> rfl

end FKMedialTurningFiber
end
end StatMech.FrontierD
