/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralDecayClose.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.FK.CylinderDecayClose
open MeasureTheory Filter Topology BoundedContinuousFunction SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


theorem cdc_prod_coordCM_eq_indicator (s : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    (∏ e ∈ s, idc_coordCM e ω) = (cdc_multiOpenEvent s).indicator (fun _ => (1:ℝ)) ω := by
  simp only [idc_coordCM_apply]
  by_cases h : ω ∈ cdc_multiOpenEvent s
  · rw [Set.indicator_of_mem h]
    refine Finset.prod_eq_one fun e he => ?_
    rw [if_pos (h e he)]
  · rw [Set.indicator_of_notMem h]
    simp only [cdc_multiOpenEvent, Set.mem_setOf_eq, not_forall] at h
    obtain ⟨e, he, hee⟩ := h
    refine Finset.prod_eq_zero he ?_
    rw [if_neg (by simpa using hee)]


theorem cdc_multiOpenEvent_isIncreasing (s : Finset (Sym2 (Site d))) :
    IsIncreasing (cdc_multiOpenEvent s) := by
  intro a b hab ha e he
  have hle := hab e
  rw [ha e he] at hle
  exact le_antisymm (by simp) hle


theorem cdc_multiOpenEvent_measurable (s : Finset (Sym2 (Site d))) :
    MeasurableSet (cdc_multiOpenEvent s) := by
  have : cdc_multiOpenEvent s = ⋂ e ∈ s, {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
    ext ω; simp only [cdc_multiOpenEvent, Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.biInter s.countable_toSet (fun e _ => idc_openEdgeEvent_measurable e)


end FK
end StatMech
