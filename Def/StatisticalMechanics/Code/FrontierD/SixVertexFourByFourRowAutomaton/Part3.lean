/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part2


namespace StatMech.FrontierD

def sixVertexFourByFourAuditedFirstTransition (state : Fin 4) (middle : Fin 16) : Option (Fin 4) :=
  sixVertexFourByFourAuditedFirstStateDecode
    (sixVertexFourByFourNextVerticalRow
      (sixVertexFourByFourAuditedFirstMiddleRow middle) (sixVertexFourByFourAuditedFirstStateRow state))

def sixVertexFourByFourAuditedSecondTransition (state : Fin 4) (middle : Fin 16) : Option (Fin 4) :=
  sixVertexFourByFourAuditedSecondStateDecode
    (sixVertexFourByFourNextVerticalRow
      (sixVertexFourByFourAuditedSecondMiddleRow middle) (sixVertexFourByFourAuditedSecondStateRow state))

def sixVertexFourByFourAuditedFirstTransitionTable : Fin 4 -> Fin 16 -> Option (Fin 4) := ![
  ![some 0, some 0, some 0, some 0, some 2, some 2, none, none,
    none, none, none, none, some 0, some 0, some 0, some 0],
  ![some 1, some 1, some 1, some 1, none, none, some 3, some 3,
    none, none, none, none, some 1, some 1, some 1, some 1],
  ![some 2, some 2, some 2, some 2, none, none, none, none,
    none, none, some 0, some 0, some 2, some 2, some 2, some 2],
  ![some 3, some 3, some 3, some 3, none, none, none, none,
    some 1, some 1, none, none, some 3, some 3, some 3, some 3]
]

def sixVertexFourByFourAuditedSecondTransitionTable : Fin 4 -> Fin 16 -> Option (Fin 4) := ![
  ![none, some 2, none, none, some 0, some 0, some 0, some 0,
    some 0, some 0, some 0, some 0, none, some 2, none, none],
  ![some 3, none, none, none, some 1, some 1, some 1, some 1,
    some 1, some 1, some 1, some 1, some 3, none, none, none],
  ![none, none, some 0, none, some 2, some 2, some 2, some 2,
    some 2, some 2, some 2, some 2, none, none, some 0, none],
  ![none, none, none, some 1, some 3, some 3, some 3, some 3,
    some 3, some 3, some 3, some 3, none, none, none, some 1]
]

end StatMech.FrontierD
