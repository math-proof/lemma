/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrosscut
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotated
import Mathlib.Topology.Subpath
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

namespace ContinuousHalfPlaneCrosscut

@[simp] theorem horizontalPrefix_apply_one (a : Real)
    (root : Fin 2 → Real) (t : unitInterval) :
    horizontalPrefix a root t 1 = root 1 := by
  simp [horizontalPrefix, affinePath_apply]
  ring


theorem horizontalPrefix_disjoint_of_range_below
    {x y root : Fin 2 → Real} (a : Real) (gamma : Path x y)
    (hbelow : ∀ z ∈ Set.range gamma, z 1 < root 1) :
    Disjoint (Set.range (horizontalPrefix a root)) (Set.range gamma) := by
  rw [Set.disjoint_left]
  intro z hzPrefix hzGamma
  obtain ⟨t, rfl⟩ := hzPrefix
  have h := hbelow _ hzGamma
  rw [horizontalPrefix_apply_one] at h
  exact lt_irrefl _ h


theorem horizontalPrefix_disjoint_of_range_above
    {x y root : Fin 2 → Real} (a : Real) (gamma : Path x y)
    (habove : ∀ z ∈ Set.range gamma, root 1 < z 1) :
    Disjoint (Set.range (horizontalPrefix a root)) (Set.range gamma) := by
  rw [Set.disjoint_left]
  intro z hzPrefix hzGamma
  obtain ⟨t, rfl⟩ := hzPrefix
  have h := habove _ hzGamma
  rw [horizontalPrefix_apply_one] at h
  exact lt_irrefl _ h


theorem disjoint_of_coord_lt {A C : Set (Fin 2 → Real)} (i : Fin 2)
    (hsep : ∀ x ∈ A, ∀ y ∈ C, x i < y i) :
    Disjoint A C := by
  rw [Set.disjoint_left]
  intro z hzA hzC
  exact lt_irrefl _ (hsep z hzA z hzC)


theorem horizontalPrefix_coord_lt
    {a R : Real} {root : Fin 2 → Real}
    (ha : a < R) (hroot : root 0 < R) :
    ∀ z ∈ Set.range (horizontalPrefix a root), z 0 < R := by
  rintro z ⟨t, rfl⟩
  have ht0 := t.2.1
  have ht1 := t.2.2
  change (1 - (t : Real)) * a + (t : Real) * root 0 < R
  by_cases ht : (t : Real) = 1
  · rw [ht]
    norm_num
    exact hroot
  · have htlt : (t : Real) < 1 := lt_of_le_of_ne ht1 ht
    have hleft : 0 < (1 - (t : Real)) * (R - a) :=
      mul_pos (sub_pos.mpr htlt) (sub_pos.mpr ha)
    have hright : 0 ≤ (t : Real) * (R - root 0) :=
      mul_nonneg ht0 (sub_nonneg.mpr hroot.le)
    nlinarith


end ContinuousHalfPlaneCrosscut
end StatMech.FK.PeriodicPlanar
