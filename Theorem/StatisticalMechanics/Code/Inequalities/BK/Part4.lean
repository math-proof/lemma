/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/BK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Inequalities.BK.Part4
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace


variable {E F : Type*}


@[simp] lemma cfgEquiv_apply (e : E ≃ F) (ω : ConfigSpace F) (x : E) :
    cfgEquiv e ω x = ω (e x) := rfl

lemma cfgEquiv_mono (e : E ≃ F) {ω ω' : ConfigSpace F} (h : ω ≤ ω') :
    cfgEquiv e ω ≤ cfgEquiv e ω' := fun x => h (e x)


lemma isIncreasing_preimage (e : E ≃ F) {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    IsIncreasing ((cfgEquiv e) ⁻¹' A) := by
  intro ω ω' hωω' hω
  simp only [Set.mem_preimage] at hω ⊢
  exact hA (cfgEquiv_mono e hωω') hω

lemma agreeOn_cfgEquiv (e : E ≃ F) (K : Set E) (ωf ωf' : ConfigSpace F) :
    agreeOn (e '' K) ωf ωf' ↔ agreeOn K (cfgEquiv e ωf) (cfgEquiv e ωf') := by
  constructor
  · intro h x hx; simp only [cfgEquiv_apply]; exact h (e x) ⟨x, hx, rfl⟩
  · intro h y hy; obtain ⟨x, hx, rfl⟩ := hy; have := h x hx; simpa using this

lemma occursOn_cfgEquiv (e : E ≃ F) (A : Set (ConfigSpace E)) (K : Set E) (ωf : ConfigSpace F) :
    OccursOn ((cfgEquiv e) ⁻¹' A) (e '' K) ωf ↔ OccursOn A K (cfgEquiv e ωf) := by
  constructor
  · intro h ωe hωe
    have hsurj : ωe = cfgEquiv e ((cfgEquiv e).symm ωe) := ((cfgEquiv e).apply_symm_apply ωe).symm
    rw [hsurj]
    refine h _ ?_
    rw [agreeOn_cfgEquiv, (cfgEquiv e).apply_symm_apply ωe]; exact hωe
  · intro h ωf' hωf'; rw [agreeOn_cfgEquiv] at hωf'; exact h _ hωf'


theorem preimage_disjointOccurrence (e : E ≃ F) (A B : Set (ConfigSpace E)) :
    (cfgEquiv e) ⁻¹' (disjointOccurrence A B)
      = disjointOccurrence ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B) := by
  ext ωf
  simp only [Set.mem_preimage, mem_disjointOccurrence]
  constructor
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨e '' K, e '' L, (Set.disjoint_image_iff e.injective).mpr hKL,
      (occursOn_cfgEquiv e A K ωf).mpr hA, (occursOn_cfgEquiv e B L ωf).mpr hB⟩
  · rintro ⟨K', L', hKL', hA, hB⟩
    refine ⟨e.symm '' K', e.symm '' L', (Set.disjoint_image_iff e.symm.injective).mpr hKL', ?_, ?_⟩
    · have h := (occursOn_cfgEquiv e A (e.symm '' K') ωf).mp
      rw [Set.image_image] at h; simp only [Equiv.apply_symm_apply, Set.image_id'] at h
      exact h hA
    · have h := (occursOn_cfgEquiv e B (e.symm '' L') ωf).mp
      rw [Set.image_image] at h; simp only [Equiv.apply_symm_apply, Set.image_id'] at h
      exact h hB

lemma pweight_transfer [Fintype E] [Fintype F] (e : E ≃ F) (φ : E → Bool → ℝ)
    (ωf : ConfigSpace F) :
    pweight φ (cfgEquiv e ωf) = pweight (fun y => φ (e.symm y)) ωf := by
  simp only [pweight, cfgEquiv_apply]
  exact Fintype.prod_equiv e (fun x => φ x (ωf (e x))) (fun y => φ (e.symm y) (ωf y))
    (fun x => by simp)


lemma wprob_transfer [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (e : E ≃ F) (φ : E → Bool → ℝ) (S : Set (ConfigSpace E)) :
    wprob φ S = wprob (fun y => φ (e.symm y)) ((cfgEquiv e) ⁻¹' S) := by
  simp only [wprob]
  rw [← Equiv.sum_comp (cfgEquiv e) (fun ω => S.indicator (fun _ => (1 : ℝ)) ω * pweight φ ω)]
  apply Finset.sum_congr rfl
  intro ωf _
  rw [pweight_transfer]
  congr 1


theorem bk_wprob_general [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (hφ0 : ∀ x b, 0 ≤ φ x b) (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  classical
  set n := Fintype.card E with hn
  obtain ⟨e⟩ := Fintype.truncEquivFin E
  set ψ : Fin n → Bool → ℝ := fun y => φ (e.symm y) with hψ
  have hψ0 : ∀ i b, 0 ≤ ψ i b := fun i b => hφ0 (e.symm i) b
  have hψ1 : ∀ i, ψ i false + ψ i true = 1 := fun i => hφ1 (e.symm i)
  have hAt : IsIncreasing ((cfgEquiv e) ⁻¹' A) := isIncreasing_preimage e hA
  have hBt : IsIncreasing ((cfgEquiv e) ⁻¹' B) := isIncreasing_preimage e hB
  have hbk := bk_wprob n ψ hψ0 hψ1 ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B) hAt hBt
  rw [← preimage_disjointOccurrence e A B] at hbk
  rw [wprob_transfer e φ (disjointOccurrence A B), wprob_transfer e φ A, wprob_transfer e φ B]
  exact hbk


theorem bernoulli_real_eq_wprob [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    (S : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real S
      = wprob (fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b}) S := by
  rw [bernoulliProductMeasure.real_eq_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [bernoulliProductMeasure.real_singleton]
  rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem bk_inequality [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
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
  exact bk_wprob_general φ hφ0 hφ1 hA hB

end StatMech
