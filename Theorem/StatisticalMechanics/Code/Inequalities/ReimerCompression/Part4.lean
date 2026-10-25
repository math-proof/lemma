/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompression.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Def.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part4
open MeasureTheory Finset
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {E : Type*}


@[simp] lemma lowerCoord_self [DecidableEq E] (i : E) (ω : ConfigSpace E) :
    lowerCoord i ω i = false := by simp [lowerCoord]

lemma lowerCoord_of_ne [DecidableEq E] {i j : E} (h : j ≠ i) (ω : ConfigSpace E) :
    lowerCoord i ω j = ω j := by simp [lowerCoord, Function.update_of_ne h]

lemma cfgSupport_lowerCoord [Fintype E] [DecidableEq E] (i : E) (ω : ConfigSpace E) :
    cfgSupport (lowerCoord i ω) = (cfgSupport ω).erase i := by
  ext j
  simp only [mem_cfgSupport, lowerCoord, Function.update, Finset.mem_erase]
  by_cases h : j = i
  · subst h; simp
  · simp [h]


theorem downCompress_isDownAt [Fintype E] [DecidableEq E] (i : E) (𝒜 : Finset (ConfigSpace E))
    {ω : ConfigSpace E} (hω : ω ∈ downCompress i 𝒜) :
    lowerCoord i ω ∈ downCompress i 𝒜 := by
  rw [mem_downCompress] at hω ⊢
  rw [cfgSupport_lowerCoord]
  exact Down.erase_mem_compression_of_mem_compression hω


theorem downCompress_idem [Fintype E] [DecidableEq E] (i : E) (𝒜 : Finset (ConfigSpace E)) :
    downCompress i (downCompress i 𝒜) = downCompress i 𝒜 := by
  unfold downCompress
  have h1 : ((Down.compression i (𝒜.image cfgSupport)).image supportCfg).image cfgSupport
      = Down.compression i (𝒜.image cfgSupport) := by
    rw [Finset.image_image]
    have : (cfgSupport ∘ supportCfg) = (id : Finset E → Finset E) := by
      funext s; simp [cfgSupport_supportCfg]
    rw [this, Finset.image_id]
  rw [h1, Down.compression_idem]


lemma occursOn_univ_iff (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    OccursOn A Set.univ ω ↔ ω ∈ A := by
  refine ⟨OccursOn.mem_self, fun hω ω' hω' => ?_⟩
  have : ω' = ω := by funext i; exact hω' i (Set.mem_univ i)
  rwa [this]


lemma occursOn_empty_iff (A : Set (ConfigSpace E)) (ω : ConfigSpace E) :
    OccursOn A (∅ : Set E) ω ↔ ∀ ω', ω' ∈ A :=
  ⟨fun h ω' => h ω' (by intro e he; simp at he), fun h ω' _ => h ω'⟩


lemma fin1_coord_cases (K : Set (Fin 1)) : K = ∅ ∨ K = Set.univ := by
  by_cases h : (0 : Fin 1) ∈ K
  · right; ext i; fin_cases i; simp [h]
  · left; ext i; fin_cases i; simp [h]


lemma mem_disjointOccurrence_fin1 (A B : Set (ConfigSpace (Fin 1))) (ω : ConfigSpace (Fin 1)) :
    ω ∈ disjointOccurrence A B ↔
      ((∀ ω', ω' ∈ A) ∧ ω ∈ B) ∨ (ω ∈ A ∧ (∀ ω', ω' ∈ B)) := by
  rw [mem_disjointOccurrence]
  refine ⟨?_, ?_⟩
  · rintro ⟨K, L, hKL, hA, hB⟩
    rcases fin1_coord_cases K with hK | hK <;> rcases fin1_coord_cases L with hL | hL <;>
      subst hK <;> subst hL
    · exact Or.inl ⟨(occursOn_empty_iff A ω).mp hA, (occursOn_empty_iff B ω).mp hB ω⟩
    · exact Or.inl ⟨(occursOn_empty_iff A ω).mp hA, (occursOn_univ_iff B ω).mp hB⟩
    · exact Or.inr ⟨(occursOn_univ_iff A ω).mp hA, (occursOn_empty_iff B ω).mp hB⟩
    · exact absurd hKL (by simp)
  · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
    · exact ⟨∅, Set.univ, by simp, (occursOn_empty_iff A ω).mpr hA, (occursOn_univ_iff B ω).mpr hB⟩
    · exact ⟨Set.univ, ∅, by simp, (occursOn_univ_iff A ω).mpr hA, (occursOn_empty_iff B ω).mpr hB⟩


lemma forall_mem_fin1 (A : Set (ConfigSpace (Fin 1))) :
    (∀ ω', ω' ∈ A) ↔ ((fun _ => false) ∈ A ∧ (fun _ => true) ∈ A) := by
  refine ⟨fun h => ⟨h _, h _⟩, ?_⟩
  rintro ⟨h0, h1⟩ ω'
  rcases (show ω' = (fun _ => false) ∨ ω' = (fun _ => true) from by
    by_cases h : ω' 0 = true
    · right; funext i; fin_cases i; exact h
    · left; funext i; fin_cases i; simpa using h) with h | h
  · rwa [h]
  · rwa [h]


lemma pweight_fin1 (φ : Fin 1 → Bool → ℝ) (ω : ConfigSpace (Fin 1)) :
    pweight φ ω = φ 0 (ω 0) := by simp only [pweight, Fin.prod_univ_one]


lemma wprob_fin1 (φ : Fin 1 → Bool → ℝ) (S : Set (ConfigSpace (Fin 1))) :
    wprob φ S = S.indicator (fun _ => (1 : ℝ)) (fun _ => false) * φ 0 false
              + S.indicator (fun _ => (1 : ℝ)) (fun _ => true) * φ 0 true := by
  simp only [wprob]
  rw [show (Finset.univ : Finset (ConfigSpace (Fin 1)))
        = {(fun _ => false), (fun _ => true)} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, pweight_fin1, pweight_fin1]


theorem reimer_wprob_one (φ : Fin 1 → Bool → ℝ)
    (hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1)
    (A B : Set (ConfigSpace (Fin 1))) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  classical
  have hq0 : 0 ≤ φ 0 false := hφ0 0 false
  have hp0 : 0 ≤ φ 0 true := hφ0 0 true
  have hqp : φ 0 false + φ 0 true = 1 := hφ1 0
  rw [wprob_fin1, wprob_fin1, wprob_fin1]
  simp only [Set.indicator_apply, mem_disjointOccurrence_fin1, forall_mem_fin1]
  by_cases hAF : (fun _ => false) ∈ A <;> by_cases hAT : (fun _ => true) ∈ A <;>
    by_cases hBF : (fun _ => false) ∈ B <;> by_cases hBT : (fun _ => true) ∈ B <;>
    simp only [hAF, hAT, hBF, hBT, and_true, and_false, or_false, or_true,
      if_true, if_false, and_self] <;>
    nlinarith [hq0, hp0, hqp]


end StatMech
