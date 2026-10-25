/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part7
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem preferenceInterface_neighborFinset_left {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n) :
    (preferenceInterfaceGraph color).neighborFinset (.left) =
      (preferenceLeftActiveRows color hn).image fun j =>
        .triangle (preferenceLeftTriangle hn j) := by
  classical
  ext v
  simp only [mem_neighborFinset, Finset.mem_image, preferenceLeftActiveRows,
    Finset.mem_filter, Finset.mem_univ, true_and]
  change preferenceInterfaceAdj color .left v ↔ _
  rw [preferenceInterfaceAdj_exterior_iff color .left (by simp)]
  constructor
  · rintro ⟨t, k, hk, hother, hv⟩
    obtain ⟨hupper, hcol, rfl⟩ :=
      (preferenceTriangleOther_eq_left_iff t k).1 hother
    rcases t with ⟨i, j, upper⟩
    dsimp at hupper hcol hk hv
    subst upper
    have hi : i = (⟨0, hn⟩ : Fin n) := Fin.ext hcol
    subst i
    exact ⟨j, hk, hv.symm⟩
  · rintro ⟨j, hj, hv⟩
    exact ⟨preferenceLeftTriangle hn j, 2, hj,
      (preferenceTriangleOther_eq_left_iff _ _).2 ⟨rfl, rfl, rfl⟩,
      hv.symm⟩

theorem preferenceInterface_degree_left {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n) :
    (preferenceInterfaceGraph color).degree (.left) =
      (preferenceLeftActiveRows (n := n) (m := m) color hn).card := by
  classical
  rw [← card_neighborFinset_eq_degree,
    preferenceInterface_neighborFinset_left (hn := hn)]
  apply Finset.card_image_of_injective
  intro i j hij
  have ht : preferenceLeftTriangle hn i = preferenceLeftTriangle hn j := by
    injection hij
  exact congrArg PreferenceTriangle.row ht

end StatMech.FK.PeriodicPlanar
