/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part7


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAWReflectVertex_invol {T L : ℕ}
    (v : HexAWVertex T L) :
    hexAWReflectVertex (hexAWReflectVertex v) = v := by
  apply Subtype.ext
  exact hexAWReflectCoord_invol v.1


end
end StatMech.Universality
