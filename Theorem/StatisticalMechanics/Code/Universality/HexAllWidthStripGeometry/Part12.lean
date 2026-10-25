/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part13


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAW_mem_interior_iff {T L : ℕ}
    (e : HexAWIncidence T L) :
    e ∈ hexAWInteriorIncidences T L ↔ hexAWIsInterior e := by
  simp [hexAWInteriorIncidences]

@[simp] theorem hexAW_mem_boundary_iff {T L : ℕ}
    (e : HexAWIncidence T L) :
    e ∈ hexAWBoundaryIncidences T L ↔ ¬ hexAWIsInterior e := by
  simp [hexAWBoundaryIncidences]


theorem hexAWReflectIncidence_mem_interior_iff {T L : ℕ}
    (e : HexAWIncidence T L) :
    hexAWReflectIncidence e ∈ hexAWInteriorIncidences T L ↔
      e ∈ hexAWInteriorIncidences T L := by
  simp [hexAWIsInterior_reflect_iff]


theorem hexAWReflectIncidence_mem_boundary_iff {T L : ℕ}
    (e : HexAWIncidence T L) :
    hexAWReflectIncidence e ∈ hexAWBoundaryIncidences T L ↔
      e ∈ hexAWBoundaryIncidences T L := by
  simp [hexAWIsInterior_reflect_iff]


theorem hexAW_incidence_partition (T L : ℕ) :
    hexAWInteriorIncidences T L ∪ hexAWBoundaryIncidences T L =
      hexAWIncidences T L := by
  exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)

theorem hexAW_incidence_partition_disjoint (T L : ℕ) :
    Disjoint (hexAWInteriorIncidences T L)
      (hexAWBoundaryIncidences T L) :=
  Finset.disjoint_sdiff


end
end StatMech.Universality
