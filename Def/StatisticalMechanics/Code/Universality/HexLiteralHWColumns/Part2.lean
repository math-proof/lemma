/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns


namespace StatMech.Universality

open HexWalk

noncomputable section

def hlhc_coordBound (c : HexAWCoord) : ℕ :=
  c.i.natAbs + c.j.natAbs

end
end StatMech.Universality
