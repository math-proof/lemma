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
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

namespace ContinuousHalfPlaneCrosscut

theorem exists_parameter_coord_eq
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : start i ≤ a)
    (hfinish : a ≤ finish i) :
    ∃ t : unitInterval, gamma t i = a := by
  have hcontinuous : Continuous (fun t : unitInterval => gamma t i) :=
    continuous_apply i |>.comp gamma.continuous
  have ha : a ∈ Set.Icc ((fun t : unitInterval => gamma t i) 0)
      ((fun t : unitInterval => gamma t i) 1) := by
    simpa using ⟨hstart, hfinish⟩
  exact intermediate_value_univ (0 : unitInterval) 1 hcontinuous ha


theorem exists_parameter_coord_eq_of_ge
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : a ≤ start i)
    (hfinish : finish i ≤ a) :
    ∃ t : unitInterval, gamma t i = a := by
  have hcontinuous : Continuous (fun t : unitInterval => gamma t i) :=
    continuous_apply i |>.comp gamma.continuous
  have ha : a ∈ Set.Icc ((fun t : unitInterval => gamma t i) 1)
      ((fun t : unitInterval => gamma t i) 0) := by
    simpa using ⟨hfinish, hstart⟩
  exact intermediate_value_univ (1 : unitInterval) 0 hcontinuous ha


theorem exists_first_parameter_coord_eq
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real)
    (hne : ∃ u : unitInterval, gamma u i = a) :
    ∃ t : unitInterval, gamma t i = a ∧
      ∀ u : unitInterval, gamma u i = a → t ≤ u := by
  let K : Set unitInterval := {u | gamma u i = a}
  have hcontinuous : Continuous (fun u : unitInterval => gamma u i) :=
    continuous_apply i |>.comp gamma.continuous
  have hclosed : IsClosed K := by
    exact isClosed_eq hcontinuous continuous_const
  have hKne : K.Nonempty := by
    obtain ⟨u, hu⟩ := hne
    exact ⟨u, hu⟩
  obtain ⟨t, htK, htmin⟩ := hclosed.isCompact.exists_isMinOn
    hKne continuous_id.continuousOn
  exact ⟨t, htK, fun u hu => htmin hu⟩


theorem exists_last_parameter_coord_eq
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real)
    (hne : ∃ u : unitInterval, gamma u i = a) :
    ∃ t : unitInterval, gamma t i = a ∧
      ∀ u : unitInterval, gamma u i = a → u ≤ t := by
  let K : Set unitInterval := {u | gamma u i = a}
  have hcontinuous : Continuous (fun u : unitInterval => gamma u i) :=
    continuous_apply i |>.comp gamma.continuous
  have hclosed : IsClosed K := by
    exact isClosed_eq hcontinuous continuous_const
  have hKne : K.Nonempty := by
    obtain ⟨u, hu⟩ := hne
    exact ⟨u, hu⟩
  obtain ⟨t, htK, htmax⟩ := hclosed.isCompact.exists_isMaxOn
    hKne continuous_id.continuousOn
  exact ⟨t, htK, fun u hu => htmax hu⟩


theorem exists_first_line_contact_suffix
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : start i ≤ a)
    (hfinish : a ≤ finish i) :
    ∃ t : unitInterval,
      gamma t i = a ∧
      (∀ u : unitInterval, gamma u i = a → t ≤ u) ∧
      Set.range (gamma.subpath t 1) ⊆ Set.range gamma := by
  obtain ⟨u, hu⟩ := exists_parameter_coord_eq gamma i a hstart hfinish
  obtain ⟨t, ht, htfirst⟩ :=
    exists_first_parameter_coord_eq gamma i a ⟨u, hu⟩
  refine ⟨t, ht, htfirst, ?_⟩
  rw [Path.range_subpath]
  exact image_subset_range _ _


theorem exists_last_line_contact_prefix
    {start finish : Fin 2 → Real} (gamma : Path start finish)
    (i : Fin 2) (a : Real) (hstart : start i ≤ a)
    (hfinish : a ≤ finish i) :
    ∃ t : unitInterval,
      gamma t i = a ∧
      (∀ u : unitInterval, gamma u i = a → u ≤ t) ∧
      Set.range (gamma.subpath 0 t) ⊆ Set.range gamma := by
  obtain ⟨u, hu⟩ := exists_parameter_coord_eq gamma i a hstart hfinish
  obtain ⟨t, ht, htlast⟩ :=
    exists_last_parameter_coord_eq gamma i a ⟨u, hu⟩
  refine ⟨t, ht, htlast, ?_⟩
  rw [Path.range_subpath]
  exact image_subset_range _ _


end ContinuousHalfPlaneCrosscut
end StatMech.FK.PeriodicPlanar
