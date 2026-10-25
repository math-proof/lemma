/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part13
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def preferenceGridBoundaryToSite {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    {x // x ∈ preferenceGridBoundary color} →
      {z // z ∈ preferenceInnerBoundary
        (preferenceGridRectangle n m) (preferenceGridTrueSet color)} :=
  fun x => ⟨preferenceGridSite (n := n) (m := m)
      (x : PreferenceGridVertex n m),
    preferenceGridBoundary_site_mem_inner (n := n) (m := m) color x⟩

def preferenceGridBoundaryGraphHom {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    preferenceGridBoundaryGraph color →g
      preferenceBoundaryGraph
        (preferenceGridRectangle n m) (preferenceGridTrueSet color) where
  toFun := preferenceGridBoundaryToSite (n := n) (m := m) color
  map_rel' := by
    intro x y hxy
    unfold preferenceBoundaryGraph preferenceGridBoundaryToSite
    change KingAdj
      (preferenceGridSite (n := n) (m := m) x)
      (preferenceGridSite (n := n) (m := m) y)
    exact hxy


end StatMech.FK.PeriodicPlanar
