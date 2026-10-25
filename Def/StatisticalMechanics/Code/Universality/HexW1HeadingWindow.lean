/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.HexW1HeadingWindow.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


namespace HexWindingBound

variable {inRegion : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ} (S : HexWindingBound inRegion a h0 z)


def toBoundarySide : HexBoundarySide inRegion a h0 z where
  H := S.H
  w := S.w
  hHL := S.hHL
  hHU := S.hHU
  exits := S.exits

end HexWindingBound
end StatMech.Universality
