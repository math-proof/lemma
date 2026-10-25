/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part12
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem preferenceGridBoundary_site_mem_inner {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) :
    ∀ x : {x // x ∈ preferenceGridBoundary color},
      preferenceGridSite (n := n) (m := m) (x : PreferenceGridVertex n m) ∈
        preferenceInnerBoundary
        (preferenceGridRectangle n m) (preferenceGridTrueSet color) := by
  intro x
  have hdata := preferenceGridBoundary_color_data color x x.2
  obtain ⟨htrue, y, hxy, hfalse⟩ := hdata
  refine ⟨?_, ?_, preferenceGridSite y, ?_, hxy, ?_⟩
  · exact ⟨x, Set.mem_univ _, rfl⟩
  · exact ⟨x, htrue, rfl⟩
  · exact ⟨y, Set.mem_univ _, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have hzy : z = y := preferenceGridSite_injective heq
    subst z
    simp_all

end StatMech.FK.PeriodicPlanar
