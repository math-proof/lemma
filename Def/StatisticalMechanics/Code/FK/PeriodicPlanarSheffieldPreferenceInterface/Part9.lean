/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Inductive.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part2
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def PreferenceFlagCrossing {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) : Prop :=
  ∃ (firstTriangle : PreferenceTriangle n m) (firstSide : Fin 3),
    preferenceTriangleSideActive color firstTriangle firstSide ∧
    preferenceTriangleOther firstTriangle firstSide = .left ∧
    PreferenceRightFlagChain color firstTriangle

end StatMech.FK.PeriodicPlanar
