/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part11
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def preferenceGridBoundary {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    Set (PreferenceGridVertex n m) :=
  {x | ∃ (t : PreferenceTriangle n m) (k : Fin 3),
    preferenceTriangleSideActive color t k ∧
      x = preferenceTriangleSideTrue color t k}

def preferenceGridBoundaryGraph {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    SimpleGraph {x // x ∈ preferenceGridBoundary color} where
  Adj x y := KingAdj
    (preferenceGridSite (n := n) (m := m) x)
    (preferenceGridSite (n := n) (m := m) y)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

def preferenceSideBoundaryPoint {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3)
    (hactive : preferenceTriangleSideActive color t k) :
    {x // x ∈ preferenceGridBoundary color} :=
  ⟨preferenceTriangleSideTrue color t k, ⟨t, k, hactive, rfl⟩⟩

end StatMech.FK.PeriodicPlanar
