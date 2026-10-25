/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Def.StatisticalMechanics.Code.Walls.wcscornersum.Part4
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wcs

open StatMech.Lattice

open StatMech.Wad

open StatMech.Euc

open StatMech.Walls


open Classical in


theorem wcs_turnZ_probe (K : Set (Site 2)) (e : Dart) :
    turnZ K e =
      (if frontCell e ∈ K then 1 else if sideCell e ∈ K then 0 else -1) := by
  classical
  unfold turnZ frontCell sideCell; rfl


theorem wcs_turnZ_eq_one_iff (K : Set (Site 2)) (e : Dart) :
    turnZ K e = 1 ↔ frontCell e ∈ K := by
  classical
  rw [wcs_turnZ_probe]
  by_cases h : frontCell e ∈ K
  · simp [h]
  · simp only [h, if_false, iff_false]
    by_cases h2 : sideCell e ∈ K <;> simp [h2]


theorem wcs_turnZ_eq_negone_iff (K : Set (Site 2)) (e : Dart) :
    turnZ K e = -1 ↔ (frontCell e ∉ K ∧ sideCell e ∉ K) := by
  classical
  rw [wcs_turnZ_probe]
  by_cases h1 : frontCell e ∈ K
  · simp [h1]
  · by_cases h2 : sideCell e ∈ K
    · simp [h1, h2]
    · simp [h1, h2]


theorem wcs_turnZ_eq_zero_iff (K : Set (Site 2)) (e : Dart) :
    turnZ K e = 0 ↔ (frontCell e ∉ K ∧ sideCell e ∈ K) := by
  classical
  rw [wcs_turnZ_probe]
  by_cases h1 : frontCell e ∈ K
  · simp [h1]
  · by_cases h2 : sideCell e ∈ K
    · simp [h1, h2]
    · simp [h1, h2]


end Wcs
end StatMech
