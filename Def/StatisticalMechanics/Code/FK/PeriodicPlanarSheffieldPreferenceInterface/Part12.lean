/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part12
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def preferenceGridRectangle (n m : Nat) : Set (Site 2) :=
  preferenceGridSite '' (Set.univ : Set (PreferenceGridVertex n m))

def preferenceGridTrueSet {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) : Set (Site 2) :=
  preferenceGridSite '' {x | color x = true}


def preferenceInnerBoundary (rectangle X : Set (Site 2)) : Set (Site 2) :=
  {x | x ∈ rectangle ∧ x ∈ X ∧
    ∃ y ∈ rectangle, KingAdj x y ∧ y ∉ X}


def preferenceBoundaryGraph (rectangle X : Set (Site 2)) :
    SimpleGraph {x // x ∈ preferenceInnerBoundary rectangle X} where
  Adj x y := KingAdj (x : Site 2) (y : Site 2)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end StatMech.FK.PeriodicPlanar
