/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWDepth


namespace StatMech.Universality

open HexWalk

noncomputable section

@[simp] theorem hlhd_columnTag_card : Fintype.card HLHDColumnTag = 8 := by
  decide

end
end StatMech.Universality
