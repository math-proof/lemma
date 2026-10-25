/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBoundaryAlignedLocalObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part31


namespace StatMech.FrontierD

def boundaryAlignedTransportedLocalColor
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (entrance : Fin 4)
    (select0 select1 targetPairingP targetPairingQ layer : Bool)
    (slot : Fin 4) : Bool :=
  let baseP := strandSlot pairingP entrance
  let baseQ := boundaryAlignedSlotQRaw vertexParity
    pairingP pairingQ entrance
  let targetPairing := if layer then targetPairingQ else targetPairingP
  let branch := strandSlot targetPairing slot !=
    (if layer then baseQ else baseP)
  let selected := if branch then select1 else select0
  let sourceLayer := layer != selected
  let sourcePattern := if sourceLayer then q else p
  let sourceBase := if sourceLayer then baseQ else baseP
  let sourceSlot := if selected then
      if branch then !sourceBase else sourceBase
    else strandSlot targetPairing slot
  vertexParity ^^ horizontalSlot sourcePattern sourceSlot


def boundaryAlignedTransportedLocalPattern
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (entrance : Fin 4)
    (select0 select1 targetPairingP targetPairingQ layer : Bool) :
    SixVertexLocalIncomingPattern :=
  fun side => (vertexParity ^^ sideVertical side) ^^
    boundaryAlignedTransportedLocalColor p q pairingP pairingQ vertexParity
      entrance select0 select1 targetPairingP targetPairingQ layer side

def boundaryAlignedObstructionP : SixVertexLocalIncomingPattern :=
  ![false, true, false, true]

def boundaryAlignedObstructionQ : SixVertexLocalIncomingPattern :=
  ![false, true, true, false]

end StatMech.FrontierD
