/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part4


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAWOrigin_mem (T L : ℕ) (hT : 0 < T) :
    hexAWOriginCoord ∈ hexAWVertexSet T L := by
  simp [hexAWVertexSet, hexAWCoordBox, hexAWInStrip, hexAWOriginCoord,
    hexAWLong, hexAWTrans, hexAWDepth, hexAWBookRe2,
    hexAWBookSqrt3Im2]
  omega


end
end StatMech.Universality
