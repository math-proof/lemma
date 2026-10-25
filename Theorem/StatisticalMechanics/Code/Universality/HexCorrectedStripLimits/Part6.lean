/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part14
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part5


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCSSlantWalkHeight_spec
    {T : ℕ} {hT : 0 < T}
    (w : {ts : List ℤ // HexCSSlantWalkAtWidth T hT ts}) :
    HexCSSlantWalk T (hexCSSlantWalkHeight w) hT w.1 :=
  w.2.choose_spec

theorem hexCSSlantWalkHeight_eq
    {T L : ℕ} {hT : 0 < T}
    (w : {ts : List ℤ // HexCSSlantWalkAtWidth T hT ts})
    (hw : HexCSSlantWalk T L hT w.1) :
    hexCSSlantWalkHeight w = L :=
  hexCSSlantWalk_height_unique (hexCSSlantWalkHeight_spec w) hw

end
end StatMech.Universality
