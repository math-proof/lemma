/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripInfiniteIdentity
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumns.Part3


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hexCSInfiniteSideMassAtWidth (T : ℕ) : ℝ := by
  classical
  exact if hT : 0 < T then
    hexCSPredicateMass (HexCSSideWalkAtWidth T hT)
  else 0


noncomputable def hexCSInfiniteTopMassAtWidth (T : ℕ) : ℝ := by
  classical
  exact if hT : 0 < T then
    hexCSPredicateMass (HexCSTopWalkAtWidth T hT)
  else 0

end
end StatMech.Universality
