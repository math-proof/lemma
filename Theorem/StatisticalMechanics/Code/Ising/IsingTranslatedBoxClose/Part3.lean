/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIClose.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingCrossBoxCap.Part2
import Def.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


theorem itb_homogeneous_of_offCentre {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (g : Multiplicative (Site d)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hdom : itb_OffCentreDomination β h g) :
    iti_PlusMultiHomogeneous β h g := by
  intro T
  obtain ⟨c, hc⟩ := hdom T
  set IV_T := (plusState d β h : Measure (ConfigSpace (Site d))).real
    (fmu_multiOpen (E := Site d) T) with hivt
  set IV_T' := (plusState d β h : Measure (ConfigSpace (Site d))).real
    (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x))) with hivt'
  
  have hmid : Tendsto (fun m => (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))) atTop (𝓝 IV_T') :=
    itb_plus_multiOpen_full_tendsto hβ hh (T.image (fun x => g⁻¹ • x)) hφ hconv
  
  have hfull : Tendsto (fun m => (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop (𝓝 IV_T) :=
    itb_plus_multiOpen_full_tendsto hβ hh T hφ hconv
  
  have hup : Tendsto (fun m => (plusMeasure d (m + c) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop (𝓝 IV_T) :=
    hfull.comp (tendsto_add_atTop_nat c)
  have hlow : Tendsto (fun m => (plusMeasure d (m - c) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop (𝓝 IV_T) :=
    hfull.comp (tendsto_sub_atTop_nat c)
  
  have hle1 : IV_T ≤ IV_T' :=
    le_of_tendsto_of_tendsto hup hmid (Filter.Eventually.of_forall (fun m => (hc m).1))
  have hle2 : IV_T' ≤ IV_T :=
    le_of_tendsto_of_tendsto hmid hlow (Filter.Eventually.of_forall (fun m => (hc m).2))
  exact le_antisymm hle1 hle2


theorem itb_offCentreDomination_one (β h : ℝ) :
    itb_OffCentreDomination β h (1 : Multiplicative (Site d)) := by
  intro T
  refine ⟨0, fun m => ?_⟩
  have hTeq : T.image (fun x => (1 : Multiplicative (Site d))⁻¹ • x) = T := by
    rw [Finset.image_congr (g := id) (fun x _ => by simp), Finset.image_id]
  rw [hTeq, Nat.add_zero, Nat.sub_zero]
  exact ⟨le_refl _, le_refl _⟩


theorem itb_plusState_isTranslationInvariant_of_offCentre {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (hdom : ∀ g : Multiplicative (Site d), itb_OffCentreDomination β h g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) := by
  refine iti_plusState_isTranslationInvariant_of_homogeneous β h (fun g => ?_)
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β h
  exact itb_homogeneous_of_offCentre hβ hh g hφ hconv (hdom g)


theorem itb_plusState_isInvariantExtremePoint_of_offCentre (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ}
    (hh : 0 ≤ h) (hdom : ∀ g : Multiplicative (Site d), itb_OffCentreDomination β h g) :
    StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  icb_plusState_isInvariantExtremePoint hd hβ hh
    (itb_plusState_isTranslationInvariant_of_offCentre hβ hh hdom)


theorem itb_plusState_isErgodic_of_offCentre (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ}
    (hh : 0 ≤ h) (hdom : ∀ g : Multiplicative (Site d), itb_OffCentreDomination β h g) :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  icb_plusState_isErgodic hd hβ hh
    (itb_plusState_isTranslationInvariant_of_offCentre hβ hh hdom)

end Ising
end StatMech
