/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.CondDistribution.Part4
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Foundations.AeTailInvariant.Part2
open MeasureTheory MeasurableSpace Set Filter
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false


namespace StatMech

open ConfigSpace

variable {E H : Type*} [Countable E] [DecidableEq E]
  [Group H] [MulAction H E]


theorem atiExteriorCylinderRing_isSetRing (window : Set E) :
    IsSetRing (atiExteriorCylinderRing (E := E) window) := by
  classical
  refine ⟨⟨∅, ∅, by simp, by simp⟩, ?_, ?_⟩
  · rintro A B ⟨F, S, hF, rfl⟩ ⟨K, T, hK, rfl⟩
    refine ⟨F ∪ K,
      (Finset.restrict₂ (π := fun _ : E => Bool)
          (s := F) (t := F ∪ K) Finset.subset_union_left :
          ConfigSpace ↥(F ∪ K) → ConfigSpace F) ⁻¹' S ∪
        (Finset.restrict₂ (π := fun _ : E => Bool)
          (s := K) (t := F ∪ K) Finset.subset_union_right :
          ConfigSpace ↥(F ∪ K) → ConfigSpace K) ⁻¹' T,
      ?_, MeasureTheory.union_cylinder (α := fun _ : E => Bool) F K S T⟩
    simpa using Set.union_subset hF hK
  · rintro A B ⟨F, S, hF, rfl⟩ ⟨K, T, hK, rfl⟩
    refine ⟨F ∪ K,
      (Finset.restrict₂ (π := fun _ : E => Bool)
          (s := F) (t := F ∪ K) Finset.subset_union_left :
          ConfigSpace ↥(F ∪ K) → ConfigSpace F) ⁻¹' S ∩
        ((Finset.restrict₂ (π := fun _ : E => Bool)
          (s := K) (t := F ∪ K) Finset.subset_union_right :
          ConfigSpace ↥(F ∪ K) → ConfigSpace K) ⁻¹' T)ᶜ,
      ?_, ?_⟩
    · simpa using Set.union_subset hF hK
    · rw [diff_eq,
        MeasureTheory.compl_cylinder (α := fun _ : E => Bool),
        MeasureTheory.inter_cylinder (α := fun _ : E => Bool)]
      rfl

theorem atiExteriorCylinderRing_univ_mem (window : Set E) :
    (Set.univ : Set (ConfigSpace E)) ∈
      atiExteriorCylinderRing (E := E) window :=
  ⟨∅, Set.univ, by simp, by simp⟩

theorem ati_restrict_measurable_finSig (F : Finset E) :
    @Measurable (ConfigSpace E) (ConfigSpace F)
      (atiFinSig F) inferInstance F.restrict := by
  refine (@measurable_pi_iff (ConfigSpace E) F (fun _ => Bool)
    (atiFinSig F) _ F.restrict).mpr ?_
  intro e
  have hle : MeasurableSpace.comap (ConfigSpace.eval e.1) inferInstance ≤
      atiFinSig F := le_iSup₂_of_le e.1 e.2 le_rfl
  exact measurable_iff_comap_le.mpr hle


theorem atiExteriorCylinderRing_generateFrom (window : Set E) :
    outsideSigma window =
      generateFrom (atiExteriorCylinderRing (E := E) window) := by
  apply le_antisymm
  · change (⨆ e ∈ windowᶜ,
      MeasurableSpace.comap (ConfigSpace.eval e) inferInstance) ≤ _
    refine iSup_le fun e => iSup_le fun he => fun A hA => ?_
    obtain ⟨B, hB, rfl⟩ := hA
    apply measurableSet_generateFrom
    let S : Set (ConfigSpace ({e} : Finset E)) :=
      {eta | eta ⟨e, Finset.mem_singleton_self e⟩ ∈ B}
    refine ⟨{e}, S, ?_, ?_⟩
    · simpa using he
    · ext omega
      simp [S, MeasureTheory.cylinder, ConfigSpace.eval]
  · refine generateFrom_le ?_
    rintro A ⟨F, S, hF, rfl⟩
    have hle : atiFinSig F ≤ outsideSigma window :=
      iSup₂_mono' fun e he => ⟨e, hF he, le_rfl⟩
    exact ((ati_restrict_measurable_finSig F).mono
      hle le_rfl)
      MeasurableSet.of_discrete


theorem ati_exterior_approx_cylinder
    (window : Set E) {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    {s : Set (ConfigSpace E)}
    (hs : @MeasurableSet _ (outsideSigma window) s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (F : Finset E) (S : Set (ConfigSpace F)),
      (↑F : Set E) ⊆ windowᶜ ∧
      mu (s ∆ MeasureTheory.cylinder F S) < ε := by
  let nu : @Measure (ConfigSpace E) (outsideSigma window) :=
    mu.trim (outsideSigma_le window)
  haveI : IsFiniteMeasure nu := by
    dsimp [nu]
    infer_instance
  have hcover : ∃ D : Set (Set (ConfigSpace E)), D.Countable ∧
      D ⊆ atiExteriorCylinderRing (E := E) window ∧ nu (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, by simp⟩
    intro A hA
    rw [Set.mem_singleton_iff] at hA
    subst A
    exact atiExteriorCylinderRing_univ_mem window
  obtain ⟨A, hAmem, hclose⟩ :=
    @exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (ConfigSpace E) (outsideSigma window) nu inferInstance
      (atiExteriorCylinderRing (E := E) window)
      (atiExteriorCylinderRing_isSetRing window) hcover
      (atiExteriorCylinderRing_generateFrom window) s hs ε hε
  obtain ⟨F, S, hF, rfl⟩ := hAmem
  refine ⟨F, S, hF, ?_⟩
  have hcyl : @MeasurableSet _ (outsideSigma window)
      (MeasureTheory.cylinder F S) := by
    have hle : atiFinSig F ≤ outsideSigma window :=
      iSup₂_mono' fun e he => ⟨e, hF he, le_rfl⟩
    exact ((ati_restrict_measurable_finSig F).mono hle le_rfl)
      MeasurableSet.of_discrete
  rw [show nu (MeasureTheory.cylinder F S ∆ s) =
      mu (MeasureTheory.cylinder F S ∆ s) from
        trim_measurableSet_eq (outsideSigma_le window) (hcyl.symmDiff hs)] at hclose
  rwa [symmDiff_comm] at hclose

theorem atiShift_measurable (g : H) (F : Finset E) :
    @Measurable (ConfigSpace E) (ConfigSpace E)
      (atiFinSig (F.image (fun e => g⁻¹ • e))) (atiFinSig F) (shift g) := by
  refine Measurable.of_comap_le ?_
  rw [show atiFinSig F =
      ⨆ e ∈ F, MeasurableSpace.comap (ConfigSpace.eval e) inferInstance from rfl,
    MeasurableSpace.comap_iSup]
  refine iSup_le fun e => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun he => ?_
  rw [comap_comp]
  have heq : (ConfigSpace.eval e ∘ shift g) =
      ConfigSpace.eval (g⁻¹ • e) := by
    funext omega
    simp [ConfigSpace.eval, shift]
  rw [heq]
  exact le_iSup₂_of_le (g⁻¹ • e)
    (Finset.mem_image_of_mem _ he) le_rfl

theorem atiFinSig_le_outsideSigma (F : Finset E) (window : Set E)
    (h : (↑F : Set E) ⊆ windowᶜ) : atiFinSig F ≤ outsideSigma window :=
  iSup₂_mono' fun e he => ⟨e, h he, le_rfl⟩

theorem ati_symmDiff_preimage_invariant
    {mu : Measure (ConfigSpace E)}
    (hmu : IsTranslationInvariant (G := H) mu)
    {s A : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hA : MeasurableSet A) (g : H)
    (hinv : shift g ⁻¹' s = s) :
    mu (s ∆ (shift g ⁻¹' A)) = mu (s ∆ A) := by
  have hpre : shift g ⁻¹' (s ∆ A) = s ∆ (shift g ⁻¹' A) := by
    rw [Set.preimage_symmDiff, hinv]
  calc
    mu (s ∆ (shift g ⁻¹' A)) = mu (shift g ⁻¹' (s ∆ A)) := by rw [hpre]
    _ = mu (s ∆ A) :=
      (hmu g).measure_preimage (hs.symmDiff hA).nullMeasurableSet


theorem ati_invariant_approx
    (window : ℕ → Set E)
    (hescape : ∀ (F : Finset E) (k : ℕ), ∃ g : H,
      (↑(F.image (fun e => g⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
    {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    (hmu : IsTranslationInvariant (G := H) mu)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : H, shift g ⁻¹' s = s)
    (k : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : Set (ConfigSpace E),
      @MeasurableSet _ (outsideSigma (window k)) A ∧ mu (s ∆ A) < ε := by
  have hcover : ∃ D : Set (Set (ConfigSpace E)), D.Countable ∧
      D ⊆ atiCylinderRing E ∧ mu (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · intro A hA
      rw [Set.mem_singleton_iff] at hA
      subst A
      exact atiCylinderRing_univ_mem
    · simp
  obtain ⟨A₀, hA₀mem, hA₀close⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      atiCylinderRing_isSetRing hcover atiCylinderRing_generateFrom hs hε
  obtain ⟨F₀, hF₀⟩ := hA₀mem
  have hA₀meas : MeasurableSet A₀ :=
    (atiFinSig_le_outsideSigma F₀ (∅ : Set E) (by simp)).trans
      (outsideSigma_le _) A₀ hF₀
  obtain ⟨g, hg⟩ := hescape F₀ k
  refine ⟨shift g ⁻¹' A₀, ?_, ?_⟩
  · have hshift : @MeasurableSet _
        (atiFinSig (F₀.image (fun e => g⁻¹ • e))) (shift g ⁻¹' A₀) :=
      atiShift_measurable g F₀ hF₀
    exact atiFinSig_le_outsideSigma _ _ hg _ hshift
  · rw [ati_symmDiff_preimage_invariant hmu hs hA₀meas g (hinv g),
      symmDiff_comm s A₀]
    exact hA₀close


theorem ati_sequenceInvariant_approx
    (window : ℕ → Set E) (g : ℕ → H)
    (hescape : ∀ (F : Finset E) (k : ℕ), ∃ n : ℕ,
      (↑(F.image (fun e => (g n)⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
    {mu : Measure (ConfigSpace E)} [IsFiniteMeasure mu]
    (hmu : IsTranslationInvariant (G := H) mu)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ n : ℕ, shift (g n) ⁻¹' s = s)
    (k : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : Set (ConfigSpace E),
      @MeasurableSet _ (outsideSigma (window k)) A ∧ mu (s ∆ A) < ε := by
  have hcover : ∃ D : Set (Set (ConfigSpace E)), D.Countable ∧
      D ⊆ atiCylinderRing E ∧ mu (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, by simp⟩
    intro A hA
    rw [Set.mem_singleton_iff] at hA
    subst A
    exact atiCylinderRing_univ_mem
  obtain ⟨A₀, hA₀mem, hA₀close⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      atiCylinderRing_isSetRing hcover atiCylinderRing_generateFrom hs hε
  obtain ⟨F₀, hF₀⟩ := hA₀mem
  have hA₀meas : MeasurableSet A₀ :=
    (atiFinSig_le_outsideSigma F₀ (∅ : Set E) (by simp)).trans
      (outsideSigma_le _) A₀ hF₀
  obtain ⟨n, hn⟩ := hescape F₀ k
  refine ⟨shift (g n) ⁻¹' A₀, ?_, ?_⟩
  · have hshift : @MeasurableSet _
        (atiFinSig (F₀.image (fun e => (g n)⁻¹ • e)))
        (shift (g n) ⁻¹' A₀) :=
      atiShift_measurable (g n) F₀ hF₀
    exact atiFinSig_le_outsideSigma _ _ hn _ hshift
  · rw [ati_symmDiff_preimage_invariant hmu hs hA₀meas (g n) (hinv n),
      symmDiff_comm s A₀]
    exact hA₀close

end StatMech
