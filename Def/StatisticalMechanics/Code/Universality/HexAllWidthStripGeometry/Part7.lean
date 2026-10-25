/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part5


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWReflectVertex {T L : ℕ} (v : HexAWVertex T L) :
    HexAWVertex T L :=
  ⟨hexAWReflectCoord v.1,
    (hexAWVertexSet_reflect_iff T L v.1).2 v.2⟩

end
end StatMech.Universality
