/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part5


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def HexCSSlantWalkAtWidth (T : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  ∃ L : ℕ, HexCSSlantWalk T L hT ts

noncomputable def hexCSSlantWalkHeight
    {T : ℕ} {hT : 0 < T}
    (w : {ts : List ℤ // HexCSSlantWalkAtWidth T hT ts}) : ℕ :=
  w.2.choose

end
end StatMech.Universality
