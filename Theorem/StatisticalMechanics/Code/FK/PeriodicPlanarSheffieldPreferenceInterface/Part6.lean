/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part5
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem preferenceInterfaceAdj_triangle_iff {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (v : PreferenceInterfaceNode n m) :
    preferenceInterfaceAdj color (.triangle t) v ↔
      ∃ k : Fin 3, preferenceTriangleSideActive color t k ∧
        v = preferenceTriangleOther t k := by
  constructor
  · rintro ⟨s, k, hk, hforward | hbackward⟩
    · have hst : s = t := by simpa using hforward.1.symm
      subst s
      exact ⟨k, hk, hforward.2⟩
    · obtain ⟨l, hother, hactive⟩ :=
        preferenceTriangleOther_reciprocal color s t k hbackward.2.symm
      exact ⟨l, hactive.2 hk, hbackward.1.trans hother.symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨t, k, hk, Or.inl ⟨rfl, rfl⟩⟩

end StatMech.FK.PeriodicPlanar
