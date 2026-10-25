/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMassLimits.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumns


namespace StatMech.Universality

open HexWalk

noncomputable section

def HexCSTopWalkAnyWidth (ts : List ℤ) : Prop :=
  ∃ T : ℕ, ∃ hT : 0 < T, HexCSTopWalkAtWidth T hT ts

noncomputable def hexCSTopWalkWidth
    (w : {ts : List ℤ // HexCSTopWalkAnyWidth ts}) : ℕ :=
  w.2.choose

end
end StatMech.Universality
