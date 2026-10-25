/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness


namespace StatMech.FrontierD

def sixVertexFourByFourAuditedDecodedSeams : Fin 16 -> Fin 4 × Fin 4 := ![
  (0, 1), (0, 0), (0, 2), (0, 3),
  (1, 1), (1, 0), (1, 2), (1, 3),
  (3, 1), (3, 0), (3, 2), (3, 3),
  (2, 1), (2, 0), (2, 2), (2, 3)
]

end StatMech.FrontierD
