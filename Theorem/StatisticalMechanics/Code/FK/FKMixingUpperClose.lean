/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKMixingClose
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Def.StatisticalMechanics.Code.FK.FKMixingUpperClose
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


theorem fmu_moInd_eq_indicator (T : Finset E) (ω : ConfigSpace E) :
    fmu_moInd T ω = (fmu_multiOpen T).indicator (fun _ => (1:ℝ)) ω := by
  unfold fmu_moInd fmu_xR fmu_multiOpen; classical
  by_cases h : ω ∈ {ω : ConfigSpace E | ∀ e ∈ T, ω e = true}
  · rw [Set.indicator_of_mem h]; apply Finset.prod_eq_one; intro e he; rw [if_pos (h e he)]
  · rw [Set.indicator_of_notMem h]; simp only [Set.mem_setOf_eq, not_forall] at h
    obtain ⟨e, he, hee⟩ := h; apply Finset.prod_eq_zero he; rw [if_neg (by simpa using hee)]


theorem fmu_multiOpen_measurable [Countable E] (T : Finset E) :
    MeasurableSet (fmu_multiOpen T) := by
  have : fmu_multiOpen T = ⋂ e ∈ T, {ω : ConfigSpace E | ω e = true} := by
    ext ω; simp only [fmu_multiOpen, Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.biInter T.countable_toSet
    (fun e _ => measurableSet_eq_fun (measurable_pi_apply e) measurable_const)


theorem fmu_multiOpen_isIncreasing (T : Finset E) : IsIncreasing (fmu_multiOpen T) := by
  intro a b hab ha e he
  have hle := hab e
  rw [ha e he] at hle
  exact le_antisymm (by simp) hle


theorem fmu_shift_multiOpen [DecidableEq E] (g : G) (T : Finset E) :
    (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' (fmu_multiOpen T)
      = fmu_multiOpen (T.image (fun e => g⁻¹ • e)) := by
  ext ω
  simp only [Set.mem_preimage, fmu_multiOpen, Set.mem_setOf_eq, shift_apply, Finset.mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]


theorem fmu_indicator_mul_indicator (A B : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    A.indicator (fun _ => (1:ℝ)) ω * B.indicator (fun _ => (1:ℝ)) ω
      = (A ∩ B).indicator (fun _ => (1:ℝ)) ω := by
  rw [← Set.inter_indicator_mul]; simp


theorem fmu_moInd_comp_shift (g : G) (T : Finset E) (ω : ConfigSpace E) :
    fmu_moInd T (shift g ω)
      = ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T).indicator
          (fun _ => (1:ℝ)) ω := by
  rw [fmu_moInd_eq_indicator]
  exact (Set.indicator_comp_right (s := fmu_multiOpen T)
    (f := (shift g : ConfigSpace E → ConfigSpace E)) (g := fun _ => (1:ℝ)) (x := ω)).symm


theorem fmu_moInd_mul_shift_eq [Countable E] (g : G) (T T' : Finset E) :
    (fun ω => fmu_moInd T ω * fmu_moInd T' (shift g ω))
      = (fmu_multiOpen T ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T').indicator
          (fun _ => (1:ℝ)) := by
  funext ω; rw [fmu_moInd_eq_indicator, fmu_moInd_comp_shift, fmu_indicator_mul_indicator]

variable {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]

theorem fmu_integrable_moInd [Countable E] (T : Finset E) : Integrable (fmu_moInd T) μ := by
  have : fmu_moInd T = (fmu_multiOpen T).indicator (fun _ => (1:ℝ)) := by
    funext ω; exact fmu_moInd_eq_indicator T ω
  rw [this]; exact (MeasureTheory.integrable_const (1:ℝ)).indicator (fmu_multiOpen_measurable T)

theorem fmu_integrable_moInd_mul_shift [Countable E] (g : G) (T T' : Finset E) :
    Integrable (fun ω => fmu_moInd T ω * fmu_moInd T' (shift g ω)) μ := by
  rw [fmu_moInd_mul_shift_eq g T T']
  exact (MeasureTheory.integrable_const (1:ℝ)).indicator
    ((fmu_multiOpen_measurable T).inter
      ((fmu_multiOpen_measurable T').preimage (measurable_shift g)))

theorem fmu_integral_moInd [Countable E] (T : Finset E) :
    (∫ ω, fmu_moInd T ω ∂μ) = μ.real (fmu_multiOpen T) := by
  simp_rw [fmu_moInd_eq_indicator]
  rw [MeasureTheory.integral_indicator_const (1:ℝ) (fmu_multiOpen_measurable T)]; simp


end FK
end StatMech
