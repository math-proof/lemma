/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessDensity
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose2
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Def.StatisticalMechanics.Code.FK.FKUniquenessSkeleton
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {E : Type*} [Fintype E] [DecidableEq E]


variable {d : ℕ}


theorem fuc_freeMass_nonneg (d N : ℕ) (t : ℝ) : 0 ≤ fuc_freeMass d N t :=
  fun _ => measureReal_nonneg

theorem fuc_wiredMass_nonneg (d N : ℕ) (t : ℝ) : 0 ≤ fuc_wiredMass d N t :=
  fun _ => measureReal_nonneg

theorem fuc_freeMass_sum_one (d N : ℕ) (t : ℝ) : ∑ ω, fuc_freeMass d N t ω = 1 :=
  fuc_sum_real_preimage_eq_one _ (boxRestrict d N) (continuous_boxRestrict d N).measurable

theorem fuc_wiredMass_sum_one (d N : ℕ) (t : ℝ) : ∑ ω, fuc_wiredMass d N t ω = 1 :=
  fuc_sum_real_preimage_eq_one _ (boxRestrict d N) (continuous_boxRestrict d N).measurable


theorem fuc_eventMassProb_free (d N : ℕ) (t : ℝ)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fuc_freeMass d N t) A
      = (freeInfiniteVolume d (fsc_logistic_pos t) (fsc_logistic_lt_one t)
          (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' A) := by
  unfold eventMassProb fuc_freeMass
  rw [fuc_real_preimage_eq_indicator_sum _ (boxRestrict d N)
    (continuous_boxRestrict d N).measurable A]


theorem fuc_eventMassProb_wired (d N : ℕ) (t : ℝ)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fuc_wiredMass d N t) A
      = (wiredInfiniteVolume d (fsc_logistic_pos t) (fsc_logistic_lt_one t)
          (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' A) := by
  unfold eventMassProb fuc_wiredMass
  rw [fuc_real_preimage_eq_indicator_sum _ (boxRestrict d N)
    (continuous_boxRestrict d N).measurable A]


theorem fuc_edgeMargProb_eq_eventMassProb (μ : ConfigSpace (Sym2 (boxVerts d N)) → ℝ)
    (e' : Sym2 (boxVerts d N)) :
    edgeMargProb μ e' = eventMassProb μ (boxEdgeOpenEvent d N e') := by
  unfold edgeMargProb eventMassProb boxEdgeOpenEvent
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hω : ω e' = true
  · simp [Set.indicator, hω]
  · simp only [Bool.not_eq_true] at hω
    simp [Set.indicator, hω]


theorem fuc_edgeMargProb_free (d N : ℕ) (t : ℝ) (e' : Sym2 (boxVerts d N)) :
    edgeMargProb (fuc_freeMass d N t) e'
      = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) := by
  rw [fuc_edgeMargProb_eq_eventMassProb, fuc_eventMassProb_free,
    freeEdgeDensity_q2_eq_real d N e' (fsc_logistic_pos t) (fsc_logistic_lt_one t)]


theorem fuc_edgeMargProb_wired (d N : ℕ) (t : ℝ) (e' : Sym2 (boxVerts d N)) :
    edgeMargProb (fuc_wiredMass d N t) e'
      = wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) := by
  rw [fuc_edgeMargProb_eq_eventMassProb, fuc_eventMassProb_wired,
    wiredEdgeDensity_q2_eq_real d N e' (fsc_logistic_pos t) (fsc_logistic_lt_one t)]


theorem fuc_freeIV_le_wiredIV (d N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)
      ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
  have htf := fk_free_infinite_measure N hp hp1 hS
  have htw := fk_wired_infinite_measure N hp hp1 hS
  refine le_of_tendsto_of_tendsto htf htw (Filter.Eventually.of_forall (fun m => ?_))
  exact freeFiniteMeasure_dominated d m hp hp1 (by norm_num)
    (boxRestrict d N ⁻¹' S)
    ((continuous_boxRestrict d N).measurable (MeasurableSet.of_discrete))
    (fun a b hab ha => hS (monotone_boxRestrict d N hab) ha)


theorem fuc_dominated (d N : ℕ) (t : ℝ) :
    measOfMass (fuc_freeMass d N t) ≼ measOfMass (fuc_wiredMass d N t) := by
  intro A _ hAinc
  
  have hfree : (measOfMass (fuc_freeMass d N t)).real A
      = eventMassProb (fuc_freeMass d N t) A := by
    rw [measOfMass_real_eq_indicator_sum _ (fuc_freeMass_nonneg d N t) A]; rfl
  have hwired : (measOfMass (fuc_wiredMass d N t)).real A
      = eventMassProb (fuc_wiredMass d N t) A := by
    rw [measOfMass_real_eq_indicator_sum _ (fuc_wiredMass_nonneg d N t) A]; rfl
  rw [hfree, hwired, fuc_eventMassProb_free, fuc_eventMassProb_wired]
  exact fuc_freeIV_le_wiredIV d N (fsc_logistic_pos t) (fsc_logistic_lt_one t) hAinc


theorem fuc_hcoup (d N : ℕ) :
    ∀ t : ℝ, ∃ P : ConfigSpace (Sym2 (boxVerts d N)) × ConfigSpace (Sym2 (boxVerts d N)) → ℝ,
      IsMonotoneCouplingFun P (fuc_freeMass d N t) (fuc_wiredMass d N t) :=
  fun t => fuc_isMonotoneCouplingFun_of_dominated
    (fuc_freeMass_nonneg d N t) (fuc_wiredMass_nonneg d N t)
    (fuc_freeMass_sum_one d N t) (fuc_wiredMass_sum_one d N t) (fuc_dominated d N t)


theorem fuc_hmono (d N : ℕ) (eb : Sym2 (boxVerts d N)) :
    Monotone (fun t => edgeMargProb (fuc_wiredMass d N t) eb) := by
  intro t1 t2 hle
  simp only [fuc_edgeMargProb_wired]
  exact wiredEdgeDensity_q2_monotoneOn d N eb (fsc_logistic_mem_Ioo t1)
    (fsc_logistic_mem_Ioo t2) (fsc_logistic_strictMono.monotone hle)


end FK
end StatMech
