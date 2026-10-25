/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCriticalDivergence
import Def.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut


namespace StatMech.Universality

open HexWalk

noncomputable section

abbrev HexCSNextTopWalk (T : ℕ) (hT : 1 ≤ T) :=
  {ts : List ℤ // HexCSTopWalkAtWidth (T + 1) (by omega) ts}

end
end StatMech.Universality
