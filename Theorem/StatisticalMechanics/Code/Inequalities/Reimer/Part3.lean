/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Def.StatisticalMechanics.Code.Inequalities.Reimer.Part3
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {E F : Type*}


@[simp] lemma flipEquiv_apply (ω : ConfigSpace E) : flipEquiv ω = flipCfg ω := rfl


lemma flipCfg_antitone {ω ω' : ConfigSpace E} (h : ω ≤ ω') : flipCfg ω' ≤ flipCfg ω := by
  intro x
  have hx := h x
  simp only [flipCfg]
  cases ha : ω x <;> cases hb : ω' x <;> simp_all [Bool.le_iff_imp]


lemma isIncreasing_flip_preimage {A : Set (ConfigSpace E)} (hA : IsDecreasing A) :
    IsIncreasing (flipCfg ⁻¹' A) := by
  intro ω ω' hωω' hω
  simp only [Set.mem_preimage] at hω ⊢
  exact hA (flipCfg_antitone hωω') hω


lemma agreeOn_flip {K : Set E} {ω ω' : ConfigSpace E} (h : agreeOn K ω ω') :
    agreeOn K (flipCfg ω) (flipCfg ω') := by
  intro e he; simp only [flipCfg]; rw [h e he]


lemma occursOn_flip_preimage (A : Set (ConfigSpace E)) (K : Set E) (ω : ConfigSpace E) :
    OccursOn (flipCfg ⁻¹' A) K ω ↔ OccursOn A K (flipCfg ω) := by
  constructor
  · intro h τ hτ
    have hω' : agreeOn K ω (flipCfg τ) := by
      have := agreeOn_flip hτ; rw [flipCfg_flipCfg] at this; exact this
    have := h (flipCfg τ) hω'
    simp only [Set.mem_preimage, flipCfg_flipCfg] at this
    exact this
  · intro h ω' hω'
    simp only [Set.mem_preimage]
    exact h _ (agreeOn_flip hω')


theorem preimage_flip_disjointOccurrence (A B : Set (ConfigSpace E)) :
    flipCfg ⁻¹' (disjointOccurrence A B)
      = disjointOccurrence (flipCfg ⁻¹' A) (flipCfg ⁻¹' B) := by
  ext ω
  simp only [Set.mem_preimage, mem_disjointOccurrence]
  constructor
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨K, L, hKL, (occursOn_flip_preimage A K ω).mpr hA,
      (occursOn_flip_preimage B L ω).mpr hB⟩
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨K, L, hKL, (occursOn_flip_preimage A K ω).mp hA,
      (occursOn_flip_preimage B L ω).mp hB⟩


lemma pweight_flip [Fintype E] (φ : E → Bool → ℝ) (ω : ConfigSpace E) :
    pweight φ (flipCfg ω) = pweight (fun x b => φ x (!b)) ω := by
  simp only [pweight, flipCfg]


lemma wprob_flip [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ) (S : Set (ConfigSpace E)) :
    wprob (fun x b => φ x (!b)) S = wprob φ (flipCfg ⁻¹' S) := by
  simp only [wprob]
  rw [← Equiv.sum_comp (flipEquiv (E := E))
    (fun ω => (flipCfg ⁻¹' S).indicator (fun _ => (1 : ℝ)) ω * pweight φ ω)]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [flipEquiv_apply]
  rw [pweight_flip]
  congr 1
  by_cases h : ω ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
    simp only [Set.mem_preimage, flipCfg_flipCfg]; exact h
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    simp only [Set.mem_preimage, flipCfg_flipCfg]; exact h


theorem bk_wprob_decreasing [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (hφ0 : ∀ x b, 0 ≤ φ x b) (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace E)} (hA : IsDecreasing A) (hB : IsDecreasing B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  have hψ0 : ∀ x b, 0 ≤ (fun x b => φ x (!b)) x b := fun x b => hφ0 x (!b)
  have hψ1 : ∀ x, (fun x b => φ x (!b)) x false + (fun x b => φ x (!b)) x true = 1 := by
    intro x; simp only [Bool.not_false, Bool.not_true]; linarith [hφ1 x]
  have hAi : IsIncreasing (flipCfg ⁻¹' A) := isIncreasing_flip_preimage hA
  have hBi : IsIncreasing (flipCfg ⁻¹' B) := isIncreasing_flip_preimage hB
  have hbk := bk_wprob_general (fun x b => φ x (!b)) hψ0 hψ1 hAi hBi
  have hidem : ∀ S : Set (ConfigSpace E), flipCfg ⁻¹' (flipCfg ⁻¹' S) = S := by
    intro S; ext ω; simp only [Set.mem_preimage, flipCfg_flipCfg]
  rw [← preimage_flip_disjointOccurrence A B] at hbk
  rw [wprob_flip φ (flipCfg ⁻¹' disjointOccurrence A B),
      wprob_flip φ (flipCfg ⁻¹' A), wprob_flip φ (flipCfg ⁻¹' B),
      hidem, hidem, hidem] at hbk
  exact hbk

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem bk_inequality_decreasing [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (hA : IsDecreasing A) (hB : IsDecreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  set φ : E → Bool → ℝ := fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b} with hφ
  have hφ0 : ∀ x b, 0 ≤ φ x b := fun _ _ => measureReal_nonneg
  have hφ1 : ∀ x, φ x false + φ x true = 1 := by
    intro _
    have h1 : (bernoulliMeasure p hp).real {false} = ((1 - p : ℝ≥0) : ℝ) := by
      rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal]
    have h2 : (bernoulliMeasure p hp).real {true} = (p : ℝ) := by
      rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal]
    simp only [hφ]
    rw [h1, h2, NNReal.coe_sub hp, NNReal.coe_one]
    ring
  rw [bernoulli_real_eq_wprob hp (disjointOccurrence A B), bernoulli_real_eq_wprob hp A,
    bernoulli_real_eq_wprob hp B]
  exact bk_wprob_decreasing φ hφ0 hφ1 hA hB

end StatMech
