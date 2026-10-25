/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3


namespace StatMech.FrontierD

def sixVertexFourByFourAuditedOppositeSeam : Fin 4 -> Fin 4 := ![2, 3, 0, 1]

def sixVertexFourByFourAuditedFirstStateRow (state : Fin 4) : SixVertexRow 4 :=
  sixVertexFourByFourRowOfMask
    (sixVertexFourByFourSectorOneSeamMask state)

def sixVertexFourByFourAuditedSecondStateRow (state : Fin 4) : SixVertexRow 4 :=
  sixVertexFourByFourRowOfMask
    (sixVertexFourByFourSectorThreeSeamMask state)

def sixVertexFourByFourAuditedFirstMiddleRow (middle : Fin 16) : SixVertexRow 4 :=
  sixVertexFourByFourRowOfMask
    (sixVertexFourByFourAuditedRowMiddle middle).1

def sixVertexFourByFourAuditedSecondMiddleRow (middle : Fin 16) : SixVertexRow 4 :=
  sixVertexFourByFourRowOfMask
    (sixVertexFourByFourAuditedRowMiddle middle).2

end StatMech.FrontierD
