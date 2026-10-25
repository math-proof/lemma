/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part5


namespace StatMech.FrontierD

noncomputable section

theorem fkMedialLocalMate_eq_localSideMate
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) (side : FKMedialSide) :
    fkMedialLocalMate pairing (v, side) =
      (v, fkMedialLocalSideMate (pairing v) side) := by
  cases hp : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, fkMedialLocalSideMate, hp]

theorem FKColoredLocalPairing.sideColor_localMate
    (cfg : FKColoredLocalPairing) (side : FKMedialSide) :
    cfg.sideColor (fkMedialLocalSideMate cfg.pairing side) =
      cfg.sideColor side := by
  cases cfg with
  | mk pairing west east =>
    cases pairing <;> cases side <;> rfl

end
end StatMech.FrontierD
