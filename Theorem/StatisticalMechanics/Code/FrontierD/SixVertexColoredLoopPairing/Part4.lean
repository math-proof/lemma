/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part2


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexCompatibleLoopPairing.toColored_incoming
    {T : EvenTorus} {omega : SixVertexArrows T}
    (pairing : SixVertexCompatibleLoopPairing omega)
    (d : FKMedialDart T) :
    pairing.toColored.incoming d = fkMedialDartIncoming omega d := by
  change (fkMedialCheckerColor d ^^
      (fkMedialCheckerColor d ^^ fkMedialDartIncoming omega d)) =
    fkMedialDartIncoming omega d
  generalize hc : fkMedialCheckerColor d = c
  generalize hi : fkMedialDartIncoming omega d = i
  cases c <;> cases i <;> rfl

@[simp] theorem SixVertexCompatibleLoopPairing.toColored_arrows
    {T : EvenTorus} {omega : SixVertexArrows T}
    (pairing : SixVertexCompatibleLoopPairing omega) :
    pairing.toColored.arrows = omega := by
  ext v
  · change (!pairing.toColored.incoming (v, .east)) = omega.horizontal v
    rw [pairing.toColored_incoming]
    simp [fkMedialDartIncoming, fkLoopEastIncoming]
  · change (!pairing.toColored.incoming (v, .north)) = omega.vertical v
    rw [pairing.toColored_incoming]
    simp [fkMedialDartIncoming, fkLoopNorthIncoming]


end
end StatMech.FrontierD
