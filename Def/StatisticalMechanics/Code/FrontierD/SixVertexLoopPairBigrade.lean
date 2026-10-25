/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade


namespace StatMech.FrontierD

noncomputable section

def sixVertexArrowPairStrandSlotColor
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (slot : FKLayeredStrandSlot T) : Bool :=
  let arrows := if slot.1 then eta else omega
  if slot.2.2 then
    fkMedialCheckerColor (slot.2.1, .east) ^^
      fkMedialDartIncoming arrows (slot.2.1, .east)
  else
    fkMedialCheckerColor (slot.2.1, .west) ^^
      fkMedialDartIncoming arrows (slot.2.1, .west)

def sixVertexArrowPairTrueStrandSlotCount
    {T : EvenTorus} (omega eta : SixVertexArrows T) : Nat :=
  Fintype.card {slot : FKLayeredStrandSlot T //
    sixVertexArrowPairStrandSlotColor omega eta slot = true}


def sixVertexConfigurationPairBigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) : Nat × Nat :=
  (sixVertexConfigurationPairTotalC pair,
    sixVertexArrowPairTrueStrandSlotCount pair.1.1 pair.2.1)


def sixVertexLoopDecoratedPairColored
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    FKColoredLoopPairingPair T
  | false => decorated.2.1.toColored
  | true => decorated.2.2.toColored

end
end StatMech.FrontierD
