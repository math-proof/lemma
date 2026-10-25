/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3


namespace StatMech.Universality

open HexWalk


def hlha_negCoord (p : HexReturnCoord) : HexReturnCoord :=
  ⟨-p.x, -p.y⟩

def hlha_swapCoord (p : HexReturnCoord) : HexReturnCoord :=
  ⟨p.y, p.x⟩

end StatMech.Universality
