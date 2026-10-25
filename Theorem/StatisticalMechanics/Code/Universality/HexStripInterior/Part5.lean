/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Def.StatisticalMechanics.Code.Universality.HexStripInterior.Part5


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexStrip_singleRight_side_exit_fires (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
    (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
    hexInfra_midAccum a h0 [(-1 : ℤ)] + HexWalk.halfStep (hexInfra_headAccum h0 [(-1 : ℤ)])
      = (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)))
        + HexWalk.halfStep ((hexStrip_singleRight_straightSide a h0 inReg hclass).H) :=
  (hexStrip_singleRight_straightSide a h0 inReg hclass).side_exit (-1) []
    ⟨hexW1Exit_singleRight_legal a h0, hstay, hexW1Exit_singleRight_endsAt a h0⟩

end StatMech.Universality
