/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part8


namespace StatMech.Universality

open HexWalk

noncomputable section

def hlhd_normalizeCoord (up : Bool) (source c : HexAWCoord) : HexAWCoord :=
  if up then
    ⟨c.i - source.i, c.j - source.j, c.color⟩
  else
    ⟨source.i - c.i, source.j - c.j, hlhd_swapColor c.color⟩

end
end StatMech.Universality
