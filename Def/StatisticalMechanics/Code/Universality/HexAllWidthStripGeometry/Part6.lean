/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part4


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWReflectCoord (c : HexAWCoord) : HexAWCoord :=
  ⟨c.j, c.i, c.color⟩


def hexAWReflectEdge (e : Fin 3) : Fin 3 :=
  match e with
  | 0 => 0
  | 1 => 2
  | 2 => 1

end
end StatMech.Universality
