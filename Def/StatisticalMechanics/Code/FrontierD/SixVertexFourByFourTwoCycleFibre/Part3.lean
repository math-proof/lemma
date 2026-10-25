/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedRowZero : Fin 16 -> Nat × Nat := ![
  (3, 3), (3, 6), (3, 9), (3, 12),
  (6, 3), (6, 6), (6, 9), (6, 12),
  (9, 3), (9, 6), (9, 9), (9, 12),
  (12, 3), (12, 6), (12, 9), (12, 12)
]

def sixVertexFourByFourAuditedRowMiddle : Fin 16 -> Nat × Nat := ![
  (0, 3), (0, 6), (0, 9), (0, 12),
  (3, 0), (3, 15), (6, 0), (6, 15),
  (9, 0), (9, 15), (12, 0), (12, 15),
  (15, 3), (15, 6), (15, 9), (15, 12)
]

def sixVertexFourByFourAuditedRowLast : Fin 4 -> Nat × Nat := ![
  (0, 0), (0, 15), (15, 0), (15, 15)
]

def sixVertexFourByFourMaskOfRowMasks (rows : Fin 4 -> Nat) : Nat :=
  Nat.ofBits fun i : Fin 16 =>
    let yx := (finProdFinEquiv (m := 4) (n := 4)).symm i
    (rows yx.1).testBit yx.2.val

end
end StatMech.FrontierD
