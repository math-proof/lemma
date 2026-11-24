module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
public import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexW1HeadingWindow.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexStripWinding.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexStripWinding_toWindingBound (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (S : HexStripWinding inRegion a h0 z)
    (hsideExit : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z →
        hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
          = z + HexWalk.halfStep S.H) :
    HexWindingBound inRegion a h0 z where
  H := S.H
  w := S.w
  hHL := S.hHL
  hHU := S.hHU
  sideExit := hsideExit
  bound := fun ts hadm => S.bound ts hadm

end StatMech.Universality
