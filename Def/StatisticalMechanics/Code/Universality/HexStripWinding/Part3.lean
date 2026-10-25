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
import Theorem.StatisticalMechanics.Code.Universality.HexStripWinding.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexStripWinding_toBoundarySide (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (S : HexStripWinding inRegion a h0 z)
    (hsideExit : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep S.H) :
    HexBoundarySide inRegion a h0 z :=
  (hexStripWinding_toWindingBound inRegion a h0 z S hsideExit).toBoundarySide


end StatMech.Universality
