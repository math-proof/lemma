/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
import Def.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity
open MeasureTheory Set
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

variable {E H : Type*} [Group H] [MulAction H E]


theorem current_exists_cylinder_symmDiff_lt [Countable E]
    (mu : Measure (InfiniteCurrentConfig E)) [IsFiniteMeasure mu]
    {A : Set (InfiniteCurrentConfig E)} (hA : MeasurableSet A)
    {epsilon : ENNReal} (hepsilon : 0 < epsilon) :
    ∃ C ∈ measurableCylinders (fun _ : E => Nat), mu (C ∆ A) < epsilon := by
  refine exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    isSetRing_measurableCylinders ?_ generateFrom_measurableCylinders.symm hA hepsilon
  exact ⟨{Set.univ}, Set.countable_singleton _,
    by simpa using univ_mem_measurableCylinders (fun _ : E => Nat), by simp⟩


theorem current_invariant_sq [Countable E]
    {mu : Measure (InfiniteCurrentConfig E)} [IsProbabilityMeasure mu]
    (hmu : CurrentIsTranslationInvariant (H := H) mu)
    (hmix : CurrentSelfMixing (H := H) mu)
    {s : Set (InfiniteCurrentConfig E)} (hs : MeasurableSet s)
    (hinv : ∀ g : H, (currentShift g) ⁻¹' s = s) :
    mu.real s = (mu.real s) ^ 2 := by
  have key : ∀ epsilon : Real, 0 < epsilon ->
      abs (mu.real s - (mu.real s) ^ 2) <= 5 * epsilon := by
    intro epsilon hepsilon
    obtain ⟨C, hCmem, hCsd⟩ := current_exists_cylinder_symmDiff_lt mu hs
      (epsilon := ENNReal.ofReal epsilon) (by simpa using hepsilon)
    have hCmeas : MeasurableSet C :=
      MeasurableSet.of_mem_measurableCylinders hCmem
    obtain ⟨g, hg⟩ := hmix C hCmem epsilon hepsilon
    let C' := (currentShift g) ⁻¹' C
    have hC'meas : MeasurableSet C' :=
      hCmeas.preimage (measurable_currentShift g)
    have hCsd' : mu.real (C ∆ s) < epsilon := by
      have h := (ENNReal.toReal_lt_toReal (measure_ne_top mu _) (by simp)).2 hCsd
      rwa [ENNReal.toReal_ofReal hepsilon.le] at h
    have hC'sd : mu.real (C' ∆ s) < epsilon := by
      have hpre : C' ∆ s = (currentShift g) ⁻¹' (C ∆ s) := by
        rw [show C' = (currentShift g) ⁻¹' C by rfl, Set.preimage_symmDiff, hinv g]
      have hmeasure : mu (C' ∆ s) = mu (C ∆ s) := by
        rw [hpre]
        exact (hmu g).measure_preimage
          ((hCmeas.symmDiff hs).nullMeasurableSet)
      rw [Measure.real, hmeasure]
      exact hCsd'
    have hCs : abs (mu.real C - mu.real s) <= mu.real (C ∆ s) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        hCmeas.nullMeasurableSet hs.nullMeasurableSet
    have hinter : abs (mu.real s - mu.real (C ∩ C')) <=
        mu.real (C ∆ s) + mu.real (C' ∆ s) := by
      have hsub : s ∆ (C ∩ C') <=
          (s ∆ C) ∪ (s ∆ C') := by
        intro x hx
        rcases hx with ⟨hxs, hxCC'⟩ | ⟨hxCC', hxs⟩
        · rw [Set.mem_inter_iff, not_and_or] at hxCC'
          rcases hxCC' with hxC | hxC'
          · exact Or.inl (Or.inl ⟨hxs, hxC⟩)
          · exact Or.inr (Or.inl ⟨hxs, hxC'⟩)
        · obtain ⟨hxC, hxC'⟩ := hxCC'
          exact Or.inl (Or.inr ⟨hxC, hxs⟩)
      calc
        abs (mu.real s - mu.real (C ∩ C'))
            <= mu.real (s ∆ (C ∩ C')) :=
          abs_measureReal_sub_le_measureReal_symmDiff hs.nullMeasurableSet
            (hCmeas.inter hC'meas).nullMeasurableSet
        _ <= mu.real ((s ∆ C) ∪ (s ∆ C')) :=
          measureReal_mono hsub (by finiteness)
        _ <= mu.real (s ∆ C) + mu.real (s ∆ C') :=
          measureReal_union_le _ _
        _ = mu.real (C ∆ s) + mu.real (C' ∆ s) := by
          rw [symmDiff_comm, symmDiff_comm s C']
    have hmix' : abs (mu.real (C ∩ C') - (mu.real C) ^ 2) < epsilon := by
      exact hg
    have hsquares : abs ((mu.real C) ^ 2 - (mu.real s) ^ 2) <=
        2 * mu.real (C ∆ s) := by
      have hCnn : 0 <= mu.real C := measureReal_nonneg
      have hsnn : 0 <= mu.real s := measureReal_nonneg
      have hCle : mu.real C <= 1 := measureReal_le_one
      have hsle : mu.real s <= 1 := measureReal_le_one
      calc
        abs (mu.real C ^ 2 - mu.real s ^ 2)
            = abs (mu.real C - mu.real s) * abs (mu.real C + mu.real s) := by
          rw [← abs_mul]
          ring_nf
        _ <= abs (mu.real C - mu.real s) * 2 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_nonneg (by positivity)]
          linarith
        _ <= mu.real (C ∆ s) * 2 :=
          mul_le_mul_of_nonneg_right hCs (by norm_num)
        _ = 2 * mu.real (C ∆ s) := by ring
    have htriangle : abs (mu.real s - (mu.real s) ^ 2) <=
        abs (mu.real s - mu.real (C ∩ C')) +
          (abs (mu.real (C ∩ C') - (mu.real C) ^ 2) +
            abs ((mu.real C) ^ 2 - (mu.real s) ^ 2)) := by
      calc
        abs (mu.real s - (mu.real s) ^ 2)
            <= abs (mu.real s - mu.real (C ∩ C')) +
                abs (mu.real (C ∩ C') - (mu.real s) ^ 2) :=
          abs_sub_le _ _ _
        _ <= abs (mu.real s - mu.real (C ∩ C')) +
              (abs (mu.real (C ∩ C') - (mu.real C) ^ 2) +
                abs ((mu.real C) ^ 2 - (mu.real s) ^ 2)) := by
          linarith [abs_sub_le (mu.real (C ∩ C'))
            ((mu.real C) ^ 2) ((mu.real s) ^ 2)]
    have hCsd0 : 0 <= mu.real (C ∆ s) := measureReal_nonneg
    have hC'sd0 : 0 <= mu.real (C' ∆ s) := measureReal_nonneg
    calc
      abs (mu.real s - (mu.real s) ^ 2)
          <= abs (mu.real s - mu.real (C ∩ C')) +
              (abs (mu.real (C ∩ C') - (mu.real C) ^ 2) +
                abs ((mu.real C) ^ 2 - (mu.real s) ^ 2)) := htriangle
      _ <= (mu.real (C ∆ s) + mu.real (C' ∆ s)) +
            (epsilon + 2 * mu.real (C ∆ s)) :=
        add_le_add hinter (add_le_add hmix'.le hsquares)
      _ <= (epsilon + epsilon) + (epsilon + 2 * epsilon) :=
        add_le_add (add_le_add hCsd'.le hC'sd.le)
          (add_le_add le_rfl (by linarith))
      _ <= 5 * epsilon := by linarith
  have hzero : abs (mu.real s - (mu.real s) ^ 2) = 0 := by
    by_contra hne
    have hpos : 0 < abs (mu.real s - (mu.real s) ^ 2) :=
      lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    have h := key (abs (mu.real s - (mu.real s) ^ 2) / 8) (by positivity)
    linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)


theorem current_real_zero_or_one
    {mu : Measure (InfiniteCurrentConfig E)} [IsProbabilityMeasure mu]
    {s : Set (InfiniteCurrentConfig E)}
    (hsq : mu.real s = (mu.real s) ^ 2) :
    mu s = 0 ∨ mu s = mu Set.univ := by
  have hreal : mu.real s = 0 ∨ mu.real s = 1 := by
    have h : mu.real s * (mu.real s - 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hreal with hzero | hone
  · left
    have h : mu s = ENNReal.ofReal (mu.real s) :=
      (ENNReal.ofReal_toReal (measure_ne_top mu s)).symm
    rw [h, hzero, ENNReal.ofReal_zero]
  · right
    rw [measure_univ]
    have h : mu s = ENNReal.ofReal (mu.real s) :=
      (ENNReal.ofReal_toReal (measure_ne_top mu s)).symm
    rw [h, hone, ENNReal.ofReal_one]


theorem current_isErgodic_of_selfMixing [Countable E]
    {mu : Measure (InfiniteCurrentConfig E)} [IsProbabilityMeasure mu]
    (hmu : CurrentIsTranslationInvariant (H := H) mu)
    (hmix : CurrentSelfMixing (H := H) mu) :
    CurrentIsErgodic (H := H) mu := by
  refine ⟨hmu, ?_⟩
  intro s hs hinv
  exact current_real_zero_or_one (current_invariant_sq hmu hmix hs hinv)


theorem current_isTranslationInvariant_of_cylinders [Countable E]
    {mu : Measure (InfiniteCurrentConfig E)} [IsProbabilityMeasure mu]
    (h : ∀ (g : H) (S : Finset E) (A : Set (↑S -> Nat)),
      mu ((currentShift g) ⁻¹' currentCylinder S A) =
        mu (currentCylinder S A)) :
    CurrentIsTranslationInvariant (H := H) mu := by
  intro g
  refine ⟨measurable_currentShift g, ?_⟩
  apply ext_of_generate_finite
    (measurableCylinders (fun _ : E => Nat))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    rw [mem_measurableCylinders] at hC
    obtain ⟨S, A, hA, rfl⟩ := hC
    rw [Measure.map_apply (measurable_currentShift g)
      (MeasurableSet.of_mem_measurableCylinders
        (cylinder_mem_measurableCylinders S A hA))]
    exact h g S A
  · rw [Measure.map_apply (measurable_currentShift g) MeasurableSet.univ]
    simp


end StatMech.FrontierB
