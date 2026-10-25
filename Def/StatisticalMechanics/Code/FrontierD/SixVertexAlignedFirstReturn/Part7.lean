/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part5
open StatMech.FrontierD


namespace StatMech.FrontierD

def boundaryAlignedSlotQRaw (vertexParity pairingP pairingQ : Bool)
    (d : Fin 4) : Bool :=
  let exit := localMate pairingP d
  let partner := localMate pairingQ exit
  let slotQ := strandSlot pairingQ partner
  let flip := (pairingP != pairingQ) &&
    (vertexParity == sideVertical exit)
  if flip then !slotQ else slotQ

def boundaryAlignedSlotQ (vertexParity : Bool)
    {p q : SixVertexLocalIncomingPattern} {d : Fin 4}
    (retie : AlignedExitRetie p q d) : Bool :=
  boundaryAlignedSlotQRaw vertexParity retie.pairingP retie.pairingQ d


def blackSideIndexOfStrandSlot
    (vertexParity pairing slot : Bool) : Bool :=
  slot ^^ (vertexParity && !pairing)

noncomputable def blackDartOfStrandSlot
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (slot : T.Vertex × Bool) : FKMedialBlackDart T :=
  (fkMedialBlackDartEquivVertexBool T).symm
    (slot.1, blackSideIndexOfStrandSlot
      (fkMedialVertexParity slot.1) (pairing slot.1) slot.2)

end StatMech.FrontierD
