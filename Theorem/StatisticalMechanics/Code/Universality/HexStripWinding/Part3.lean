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
import Def.StatisticalMechanics.Code.Universality.HexStripWinding.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


@[simp] theorem hexStripWinding_toWindingBound_H (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (S : HexStripWinding inRegion a h0 z) (hsideExit) :
    (hexStripWinding_toWindingBound inRegion a h0 z S hsideExit).H = S.H := rfl

@[simp] theorem hexStripWinding_toWindingBound_w (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (S : HexStripWinding inRegion a h0 z) (hsideExit) :
    (hexStripWinding_toWindingBound inRegion a h0 z S hsideExit).w = S.w := rfl


end StatMech.Universality
