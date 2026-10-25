/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexW1HeadingWindow.Part4
import Def.StatisticalMechanics.Code.Universality.HexStripWinding.Part6


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexStripWinding_singleRight_bound (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
    (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
    |hexInfra_headAccum h0 [(-1 : ℤ)]
        - (hexStripWinding_singleRight a h0 inReg hclass).H| < 6 :=
  (hexStripWinding_singleRight a h0 inReg hclass).bound [(-1 : ℤ)]
    ⟨hexW1Exit_singleRight_legal a h0, hstay, hexW1Exit_singleRight_endsAt a h0⟩

end StatMech.Universality
