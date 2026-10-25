/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part6


namespace StatMech.FrontierD

noncomputable section

theorem FKColoredLoopPairing.localPairing_sideColor
    {T : EvenTorus} (colored : FKColoredLoopPairing T) (v : T.Vertex)
    (side : FKMedialSide) :
    (colored.localPairing v).sideColor side = colored.color (v, side) := by
  cases hp : colored.pairing v
  · cases side
    · simp [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, hp]
    · simp [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, hp]
    · simpa [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, fkMedialLocalMate, hp] using
        (colored.color_localMate (v, .east)).symm
    · simpa [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, fkMedialLocalMate, hp] using
        (colored.color_localMate (v, .west)).symm
  · cases side
    · simp [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, hp]
    · simp [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, hp]
    · simpa [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, fkMedialLocalMate, hp] using
        (colored.color_localMate (v, .west)).symm
    · simpa [FKColoredLoopPairing.localPairing,
        FKColoredLocalPairing.sideColor, fkMedialLocalMate, hp] using
        (colored.color_localMate (v, .east)).symm


end
end StatMech.FrontierD
