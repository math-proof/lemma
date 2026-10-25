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
import Def.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


variable {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]

theorem fmu_pair_fkg_lower [Countable E] {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]
    (hμ : IsTranslationInvariant (G := G) μ)
    (hPA : ∀ {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (g : G) (T T' : Finset E) :
    μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')
      ≤ μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') := by
  have hTinc : IsIncreasing (fmu_multiOpen T) := fmu_multiOpen_isIncreasing T
  have hT'inc : IsIncreasing ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') :=
    fmc_shift_isIncreasing (fmu_multiOpen_isIncreasing T') g
  have hTmeas : MeasurableSet (fmu_multiOpen T) := fmu_multiOpen_measurable T
  have hT'meas : MeasurableSet ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') :=
    (fmu_multiOpen_measurable T').preimage (measurable_shift g)
  have hfkg := hPA hTinc hT'inc hTmeas hT'meas
  rwa [fmc_real_preimage_shift hμ g (fmu_multiOpen_measurable T')] at hfkg


theorem fmu_pairMixing_of_upperDecay [Countable E] {μ : Measure (ConfigSpace E)}
    [IsProbabilityMeasure μ]
    (hμ : IsTranslationInvariant (G := G) μ)
    (hPA : ∀ {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (hup : fmu_UpperDecay (G := G) μ) :
    fmu_PairMixing (G := G) μ := by
  intro P δ hδ
  obtain ⟨g, hg⟩ := hup P (δ / 2) (by linarith)
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  have hlow := fmu_pair_fkg_lower hμ hPA g T T'
  have hup' := hg T hT T' hT'
  
  rw [abs_of_nonneg (by linarith)]
  linarith


theorem fmu_upperDecay_dirac [Countable E] [MeasurableSingletonClass (ConfigSpace E)] :
    fmu_UpperDecay (G := G) (Measure.dirac (fun _ : E => true)) := by
  intro P δ hδ
  obtain ⟨g, hg⟩ := fmu_pairMixing_dirac (G := G) (E := E) P δ hδ
  refine ⟨g, fun T hT T' hT' => ?_⟩
  have := hg T hT T' hT'
  have h2 := (abs_lt.mp this).2
  linarith


theorem fmu_wiredIV_fkg_multiOpen {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (s₁ s₂ : Finset (Sym2 (Site d))) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₁)
      * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₂)
      ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen s₁ ∩ fmu_multiOpen s₂) := by
  classical
  
  obtain ⟨N, t, ht⟩ := cdc_finset_in_box (s₁ ∪ s₂)
  set t₁ := t.filter (fun eb => edgeIncl d N eb ∈ s₁) with ht1
  set t₂ := t.filter (fun eb => edgeIncl d N eb ∈ s₂) with ht2
  have hsplit : ∀ (sᵢ : Finset (Sym2 (Site d))) (tᵢ : Finset (Sym2 (boxVerts d N))),
      tᵢ = t.filter (fun eb => edgeIncl d N eb ∈ sᵢ) →
      (sᵢ ⊆ s₁ ∪ s₂) → sᵢ = tᵢ.image (edgeIncl d N) := by
    intro sᵢ tᵢ htᵢ hsub
    ext e
    simp only [htᵢ, Finset.mem_image, Finset.mem_filter]
    constructor
    · intro he
      have : e ∈ s₁ ∪ s₂ := hsub he
      rw [ht, Finset.mem_image] at this
      obtain ⟨eb, heb, rfl⟩ := this
      exact ⟨eb, ⟨heb, he⟩, rfl⟩
    · rintro ⟨eb, ⟨_, hin⟩, rfl⟩; exact hin
  have h1 : s₁ = t₁.image (edgeIncl d N) := hsplit s₁ t₁ ht1 Finset.subset_union_left
  have h2 : s₂ = t₂.image (edgeIncl d N) := hsplit s₂ t₂ ht2 Finset.subset_union_right
  have e1 : fmu_multiOpen s₁ = boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t₁) := by
    rw [show fmu_multiOpen s₁ = cdc_multiOpenEvent s₁ from rfl, h1,
      cdc_multiOpenEvent_image_eq_boxRestrict]
  have e2 : fmu_multiOpen s₂ = boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t₂) := by
    rw [show fmu_multiOpen s₂ = cdc_multiOpenEvent s₂ from rfl, h2,
      cdc_multiOpenEvent_image_eq_boxRestrict]
  rw [e1, e2]
  exact ivp_iv_fkg_wired N hp hp1 (cdc_boxMultiOpenEvent_isIncreasing N t₁)
    (cdc_boxMultiOpenEvent_isIncreasing N t₂)


theorem fmu_wiredIV_pairMixing_of_upperDecay {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    fmu_PairMixing (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  classical
  set μ := (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
    : Measure (ConfigSpace (Sym2 (Site d)))) with hμdef
  have hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ :=
    flc_wiredIV_isTranslationInvariant hp hp1
  intro P δ hδ
  obtain ⟨g, hg⟩ := hup P (δ / 2) (by linarith)
  refine ⟨g, ?_⟩
  intro T hT T' hT'
  
  have hlow : μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')
      ≤ μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen T') := by
    rw [fmu_shift_multiOpen g T']
    have hfkg := fmu_wiredIV_fkg_multiOpen hp hp1 T (T'.image (fun e => g⁻¹ • e))
    
    have htrans : μ.real (fmu_multiOpen (T'.image (fun e => g⁻¹ • e))) = μ.real (fmu_multiOpen T') := by
      rw [← fmu_shift_multiOpen g T']
      exact fmc_real_preimage_shift hμ g (fmu_multiOpen_measurable T')
    rw [htrans] at hfkg
    exact hfkg
  have hup' := hg T hT T' hT'
  rw [abs_of_nonneg (by linarith)]
  linarith


variable {d : ℕ}


theorem fmu_wiredIV_isErgodic_of_pairMixing {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hmix : fmu_PairMixing (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmu_isErgodic_of_pairMixing (flc_wiredIV_isTranslationInvariant hp hp1) hmix


theorem fmu_wiredIV_isErgodic_of_upperDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hup : fmu_UpperDecay (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmu_wiredIV_isErgodic_of_pairMixing hp hp1 (fmu_wiredIV_pairMixing_of_upperDecay hp hp1 hup)


theorem fmu_freeIV_isErgodic_of_pairMixing {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hmix : fmu_PairMixing (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmu_isErgodic_of_pairMixing (bdp_freeIV_isTranslationInvariant hp hp1) hmix

end FK
end StatMech
