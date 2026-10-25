/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part3
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem boolTriangleTransitionCount_even (a b c : Bool) :
    Even (boolTriangleTransitionCount a b c) := by
  cases a <;> cases b <;> cases c <;>
    simp [boolTriangleTransitionCount]


end StatMech.FK.PeriodicPlanar
