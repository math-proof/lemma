/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part7


namespace StatMech.Universality

open HexWalk

noncomputable section

@[simp] theorem hlhd_swapColor_invol (c : HexAWColor) :
    hlhd_swapColor (hlhd_swapColor c) = c := by
  cases c <;> rfl


end
end StatMech.Universality
