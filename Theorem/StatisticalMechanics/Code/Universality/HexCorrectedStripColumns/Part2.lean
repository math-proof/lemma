/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMassLimits.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripColumns


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCSTopWalkWidth_pos
    (w : {ts : List ℤ // HexCSTopWalkAnyWidth ts}) :
    0 < hexCSTopWalkWidth w :=
  w.2.choose_spec.choose

theorem hexCSTopWalkWidth_spec
    (w : {ts : List ℤ // HexCSTopWalkAnyWidth ts}) :
    HexCSTopWalkAtWidth (hexCSTopWalkWidth w)
      (hexCSTopWalkWidth_pos w) w.1 :=
  w.2.choose_spec.choose_spec

theorem hexCSTopWalkWidth_eq
    (w : {ts : List ℤ // HexCSTopWalkAnyWidth ts})
    {T : ℕ} (hT : 0 < T) (hw : HexCSTopWalkAtWidth T hT w.1) :
    hexCSTopWalkWidth w = T :=
  hexCSTopWalkAtWidth_width_unique (hexCSTopWalkWidth_spec w) hw

end
end StatMech.Universality
