/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.KingmanFilling.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.AnimalLLNas.Part2
open MeasureTheory Filter Topology Finset
open StatMech.Kingman StatMech.KingmanAE StatMech.KingmanFilling


namespace StatMech

namespace BeffaraDC

theorem prefix_le_animalValue {ω : ℤ → ℝ} (n : ℕ) {a : ℕ} (ha : a ≤ n) :
    (∑ i ∈ range a, ω (i : ℤ)) ≤ animalValue ω n :=
  Finset.le_sup' (fun a => ∑ i ∈ range a, ω (i : ℤ)) (Finset.mem_range.mpr (by omega))


theorem animalValue_le_iff {ω : ℤ → ℝ} {n : ℕ} {c : ℝ} :
    animalValue ω n ≤ c ↔ ∀ a ≤ n, (∑ i ∈ range a, ω (i : ℤ)) ≤ c := by
  unfold animalValue
  rw [Finset.sup'_le_iff]
  exact ⟨fun h a ha => h a (Finset.mem_range.mpr (by omega)),
    fun h a ha => h a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))⟩


theorem animalValue_nonneg (ω : ℤ → ℝ) (n : ℕ) : 0 ≤ animalValue ω n := by
  have := prefix_le_animalValue (ω := ω) n (a := 0) (Nat.zero_le n)
  simpa using this


theorem animalValue_subadditive (ω : ℤ → ℝ) (m n : ℕ) :
    animalValue ω (m + n) ≤ animalValue ω m + animalValue (shiftEnv^[m] ω) n := by
  rw [animalValue_le_iff]
  intro a ha
  by_cases hcase : a ≤ m
  · calc ∑ i ∈ range a, ω (i : ℤ) ≤ animalValue ω m := prefix_le_animalValue m hcase
      _ ≤ animalValue ω m + animalValue (shiftEnv^[m] ω) n := by
          have := animalValue_nonneg (shiftEnv^[m] ω) n; linarith
  · simp only [not_le] at hcase
    obtain ⟨k, rfl⟩ : ∃ k, a = m + k := ⟨a - m, by omega⟩
    have hk : k ≤ n := by omega
    have hsplit : ∑ i ∈ range (m + k), ω (i : ℤ)
        = (∑ i ∈ range m, ω (i : ℤ)) + ∑ j ∈ range k, ω ((m : ℤ) + j) := by
      rw [Finset.sum_range_add (fun x => ω (x : ℤ)) m k]; simp only [Nat.cast_add]
    rw [hsplit]
    have h1 : (∑ i ∈ range m, ω (i : ℤ)) ≤ animalValue ω m := prefix_le_animalValue m (le_refl m)
    have h2 : (∑ j ∈ range k, ω ((m : ℤ) + j)) ≤ animalValue (shiftEnv^[m] ω) n := by
      have heq : (∑ j ∈ range k, ω ((m : ℤ) + j)) = ∑ j ∈ range k, (shiftEnv^[m] ω) (j : ℤ) := by
        apply Finset.sum_congr rfl; intro j _; rw [shiftEnv_iterate]; ring_nf
      rw [heq]; exact prefix_le_animalValue n hk
    linarith


theorem animalValue_le_posSum (ω : ℤ → ℝ) (n : ℕ) :
    animalValue ω n ≤ ∑ i ∈ range n, (ω (i : ℤ))⁺ := by
  rw [animalValue_le_iff]
  intro a ha
  calc ∑ i ∈ range a, ω (i : ℤ) ≤ ∑ i ∈ range a, (ω (i : ℤ))⁺ := by
        apply Finset.sum_le_sum; intro i _; exact le_max_left _ _
    _ ≤ ∑ i ∈ range n, (ω (i : ℤ))⁺ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ha)
        intro i _ _; positivity


theorem measurable_animalValue (n : ℕ) : Measurable (fun ω : ℤ → ℝ => animalValue ω n) := by
  have hrw : (fun ω : ℤ → ℝ => animalValue ω n)
      = (range (n + 1)).sup' (by simp) (fun a => fun ω : ℤ → ℝ => ∑ i ∈ range a, ω (i : ℤ)) := by
    funext ω; rw [animalValue, Finset.sup'_apply]
  rw [hrw]
  exact measurable_sup' (by simp)
    (fun a _ => Finset.measurable_sum _ (fun i _ => measurable_pi_apply _))

variable {ρ : Measure ℝ}


theorem integrable_coord [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) (i : ℤ) :
    Integrable (fun ω : ℤ → ℝ => ω i) (Measure.infinitePi (fun _ : ℤ => ρ)) := by
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℤ => ρ) i
  have := (hmp.integrable_comp (g := (id : ℝ → ℝ)) hρ.aestronglyMeasurable).mpr hρ
  simpa using this


theorem integrable_animalValue [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) (n : ℕ) :
    Integrable (fun ω : ℤ → ℝ => animalValue ω n) (Measure.infinitePi (fun _ : ℤ => ρ)) := by
  set μ := Measure.infinitePi (fun _ : ℤ => ρ) with hμ
  have hdom : Integrable (fun ω : ℤ → ℝ => ∑ i ∈ range n, (ω (i : ℤ))⁺) μ := by
    refine integrable_finsetSum _ (fun i _ => ?_)
    exact (integrable_coord hρ (i : ℤ)).pos_part
  refine Integrable.mono' hdom (measurable_animalValue n).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (animalValue_nonneg ω n)]
  exact animalValue_le_posSum ω n


theorem animalCocycle [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) :
    SubadditiveCocycle shiftEnv (Measure.infinitePi (fun _ : ℤ => ρ))
      (fun n ω => animalValue ω n) where
  measurePreserving := shiftEnv_measurePreserving ρ
  integrable := integrable_animalValue hρ
  subadditive := fun m n => Filter.Eventually.of_forall (fun ω => animalValue_subadditive ω m n)


theorem animalValue_nonneg_ae [IsProbabilityMeasure ρ] (n : ℕ) :
    0 ≤ᵐ[Measure.infinitePi (fun _ : ℤ => ρ)] (fun ω => animalValue ω n) :=
  Filter.Eventually.of_forall (fun ω => animalValue_nonneg ω n)


theorem animalValue_lln_ae [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)),
      Tendsto (fun n => animalValue ω n / n) atTop
        (𝓝 (kingmanLimit shiftEnv (fun n ω => animalValue ω n) ω)) :=
  tendsto_div_kingmanLimit_ae_of_nonneg (animalCocycle hρ) (fun n => animalValue_nonneg_ae n)


end BeffaraDC
end StatMech
