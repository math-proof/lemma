/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkColoredLayeredSlotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (slot : FKLayeredStrandSlot T) : Bool :=
  if slot.2.2 then (source slot.1).color (slot.2.1, .east)
  else (source slot.1).color (slot.2.1, .west)


def fkColoredSideSlot (pairing : Bool) (side : FKMedialSide) : Bool :=
  match pairing, side with
  | false, .west | false, .north => false
  | false, .east | false, .south => true
  | true, .west | true, .south => false
  | true, .east | true, .north => true

end
end StatMech.FrontierD
