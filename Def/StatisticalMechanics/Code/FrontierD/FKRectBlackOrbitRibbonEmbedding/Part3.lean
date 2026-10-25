/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part2


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectMedialRibbonBlockDirection
    (pairing : Bool) (side : FKMedialSide) (t : Fin 8) : Fin 4 := by
  let block := fkRectMedialRibbonBlock pairing side
  have hlen : block.length = 8 :=
    fkRectMedialRibbonBlock_length pairing side
  exact block.get ⟨t.val, by simpa [hlen] using t.isLt⟩


def fkRectMedialRibbonBlockOffset
    (pairing : Bool) (side : FKMedialSide) (t : Fin 8) : Int × Int :=
  fkRectMedialRibbonPortOffset side +
    pos (fkRectMedialRibbonBlockDirection pairing side) t

def fkRectMedialRibbonBlockOffsetTable
    (pairing : Bool) (side : FKMedialSide) : Fin 8 → Int × Int :=
  match pairing, side with
  | false, .west => ![(2, 4), (2, 5), (2, 6), (3, 6),
      (4, 6), (4, 7), (4, 8), (4, 9)]
  | false, .east => ![(6, 4), (6, 3), (6, 2), (5, 2),
      (4, 2), (4, 1), (4, 0), (4, -1)]
  | false, .south => ![(4, 2), (5, 2), (6, 2), (6, 3),
      (6, 4), (7, 4), (8, 4), (9, 4)]
  | false, .north => ![(4, 6), (3, 6), (2, 6), (2, 5),
      (2, 4), (1, 4), (0, 4), (-1, 4)]
  | true, .west => ![(2, 4), (2, 3), (2, 2), (3, 2),
      (4, 2), (4, 1), (4, 0), (4, -1)]
  | true, .east => ![(6, 4), (6, 5), (6, 6), (5, 6),
      (4, 6), (4, 7), (4, 8), (4, 9)]
  | true, .south => ![(4, 2), (3, 2), (2, 2), (2, 3),
      (2, 4), (1, 4), (0, 4), (-1, 4)]
  | true, .north => ![(4, 6), (5, 6), (6, 6), (6, 5),
      (6, 4), (7, 4), (8, 4), (9, 4)]

end
end StatMech.FrontierD
