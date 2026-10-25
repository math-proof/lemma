/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part4


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexCSReflectVertex_invol {T L : ℕ}
    (v : HexCSVertex T L) :
    hexCSReflectVertex (hexCSReflectVertex v) = v := by
  apply Subtype.ext
  exact hexAWReflectCoord_invol v.1


end
end StatMech.Universality
