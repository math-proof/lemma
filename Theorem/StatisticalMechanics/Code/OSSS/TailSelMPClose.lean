/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailSelMP.Part3
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem tsc_restrictedSum_of_recover {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : ℕ → Set α} {Φ : ℕ → α → β} {R : β → ℕ}
    (hSmeas : ∀ k, MeasurableSet (S k)) (hSdisj : Pairwise (Function.onFun Disjoint S))
    (hScover : ⋃ k, S k = Set.univ) (hΦmeas : ∀ k, Measurable (Φ k)) (hRmeas : Measurable R)
    (hMP : ∀ k, MeasurePreserving (Φ k) μ ν)
    (hSsub : ∀ k, S k ⊆ Φ k ⁻¹' (R ⁻¹' {k})) :
    (Measure.sum (fun k => Measure.map (Φ k) (μ.restrict (S k)))) = ν := by
  ext T hT
  rw [Measure.sum_apply _ hT]
  
  have hsummand : ∀ (T : Set β), MeasurableSet T → ∀ k,
      Measure.map (Φ k) (μ.restrict (S k)) T = μ (S k ∩ Φ k ⁻¹' T) := by
    intro T hT k
    rw [Measure.map_apply (hΦmeas k) hT, Measure.restrict_apply ((hΦmeas k) hT), Set.inter_comm]
  
  have hub : ∀ (T : Set β), MeasurableSet T → ∀ k,
      μ (S k ∩ Φ k ⁻¹' T) ≤ ν (R ⁻¹' {k} ∩ T) := by
    intro T hT k
    calc μ (S k ∩ Φ k ⁻¹' T) ≤ μ (Φ k ⁻¹' (R ⁻¹' {k}) ∩ Φ k ⁻¹' T) :=
          measure_mono (Set.inter_subset_inter_left _ (hSsub k))
      _ = μ (Φ k ⁻¹' (R ⁻¹' {k} ∩ T)) := by rw [Set.preimage_inter]
      _ = ν (R ⁻¹' {k} ∩ T) := by
            rw [← (hMP k).measure_preimage
              ((hRmeas (measurableSet_singleton k)).inter hT).nullMeasurableSet]
  
  have hRpart : (⋃ k, R ⁻¹' {k}) = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨R y, rfl⟩
  have hRdisj : Pairwise (Function.onFun Disjoint (fun k => R ⁻¹' {k})) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hyi hyj
    exact hij (by rw [← hyi, hyj])
  have hRtsum : ∀ (T : Set β), MeasurableSet T → (∑' k, ν (R ⁻¹' {k} ∩ T)) = ν T := by
    intro T hT
    rw [← measure_iUnion
      (fun i j hij => (hRdisj hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun k => (hRmeas (measurableSet_singleton k)).inter hT)]
    congr 1
    rw [← Set.iUnion_inter, hRpart, Set.univ_inter]
  
  simp_rw [hsummand T hT]
  set a : ℕ → ENNReal := fun k => μ (S k ∩ Φ k ⁻¹' T) with ha
  set b : ℕ → ENNReal := fun k => μ (S k ∩ Φ k ⁻¹' Tᶜ) with hb
  
  have hab : ∀ k, a k + b k = μ (S k) := by
    intro k
    rw [ha, hb, ← measure_union]
    · congr 1
      rw [← Set.inter_union_distrib_left, ← Set.preimage_union, Set.union_compl_self,
        Set.preimage_univ, Set.inter_univ]
    · refine Disjoint.mono Set.inter_subset_right Set.inter_subset_right ?_
      have hd : Disjoint T Tᶜ := disjoint_compl_right
      exact hd.preimage (Φ k)
    · exact (hSmeas k).inter ((hΦmeas k) hT.compl)
  
  have hsumab : (∑' k, a k) + (∑' k, b k) = ν Set.univ := by
    rw [← ENNReal.tsum_add, show (fun k => a k + b k) = (fun k => μ (S k)) from funext hab,
      ← measure_iUnion hSdisj hSmeas, hScover, measure_univ, measure_univ]
  have hsuma_le : (∑' k, a k) ≤ ν T :=
    le_trans (ENNReal.tsum_le_tsum (hub T hT)) (le_of_eq (hRtsum T hT))
  have hsumb_le : (∑' k, b k) ≤ ν Tᶜ :=
    le_trans (ENNReal.tsum_le_tsum (hub Tᶜ hT.compl)) (le_of_eq (hRtsum Tᶜ hT.compl))
  have hnu : ν Set.univ = ν T + ν Tᶜ := by
    rw [← measure_union disjoint_compl_right hT.compl, Set.union_compl_self]
  rw [hnu] at hsumab
  
  by_contra hne
  have hlt : (∑' k, a k) < ν T := lt_of_le_of_ne hsuma_le hne
  have hsumb_fin : (∑' k, b k) ≠ ⊤ := ne_top_of_le_ne_top (measure_lt_top ν Tᶜ).ne hsumb_le
  have hcontra : (∑' k, a k) + (∑' k, b k) < ν T + ν Tᶜ :=
    ENNReal.add_lt_add_of_lt_of_le hsumb_fin hlt hsumb_le
  rw [hsumab] at hcontra
  exact lt_irrefl _ hcontra


lemma tsc_prefixSet_mono {n : ℕ} (σ : Fin n → E) {j k : ℕ} (hjk : j ≤ k) :
    prefixSet σ j ⊆ prefixSet σ k := by
  intro e he
  rw [mem_prefixSet_iff] at he ⊢
  obtain ⟨s, hs, rfl⟩ := he
  exact ⟨s, by omega, rfl⟩


lemma tsc_detAtC_transport {n : ℕ} (σ : Fin n → E) (f : ConfigSpace E → ℝ)
    (X X' : ConfigSpace E) (k : ℕ) (hagree : ∀ e ∈ prefixSet σ k, X e = X' e)
    (j : ℕ) (hjk : j ≤ k) (hdet : detAtC σ f X j) : detAtC σ f X' j := by
  have hagj : ∀ e ∈ prefixSet σ j, X' e = X e :=
    fun e he => (hagree e (tsc_prefixSet_mono σ hjk he)).symm
  have hfXX' : f X' = f X := hdet X' hagj
  intro w hw
  have hwX : ∀ e ∈ prefixSet σ j, w e = X e := fun e he => by rw [hw e he, ← hagj e he]
  rw [hdet w hwX, ← hfXX']


lemma tsc_stopValC_determinesC {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (X : ConfigSpace E) : detAtC (σ : Fin n → E) f X (stopValC σ f X) :=
  Nat.find_spec (⟨n, detAtC_card σ f X⟩ : ∃ t, detAtC (σ : Fin n → E) f X t)


theorem tsc_stopValC_stable {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (X X' : ConfigSpace E) (k : ℕ)
    (hagree : ∀ e ∈ prefixSet (σ : Fin n → E) k, X e = X' e)
    (hk : stopValC σ f X = k) : stopValC σ f X' = k := by
  have hdetXk : detAtC (σ : Fin n → E) f X k := hk ▸ tsc_stopValC_determinesC σ f X
  have hagree' : ∀ e ∈ prefixSet (σ : Fin n → E) k, X' e = X e := fun e he => (hagree e he).symm
  have hdetX'k : detAtC (σ : Fin n → E) f X' k :=
    tsc_detAtC_transport (σ : Fin n → E) f X X' k hagree k (le_refl k) hdetXk
  refine le_antisymm (Nat.find_le hdetX'k) ?_
  by_contra hlt
  rw [not_le] at hlt
  set j := stopValC σ f X' with hj
  have hjlt : j < k := hlt
  have hdetX'j : detAtC (σ : Fin n → E) f X' j := tsc_stopValC_determinesC σ f X'
  have hdetXj : detAtC (σ : Fin n → E) f X j :=
    tsc_detAtC_transport (σ : Fin n → E) f X' X k hagree' j (le_of_lt hjlt) hdetX'j
  have : k ≤ j := hk ▸ Nat.find_le hdetXj
  omega


lemma tsc_acp_join_head {n : ℕ} (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) (i : Fin n) (hi : (i : ℕ) < t) :
    acp_join t A B i = A ⟨i, hi⟩ := by
  unfold acp_join ubfSplit
  rw [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]; simp [hi]


lemma tsc_acp_join_tail {n : ℕ} (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) (i : Fin n) (hi : ¬ (i : ℕ) < t) :
    acp_join t A B i = B ⟨i, hi⟩ := by
  unfold acp_join ubfSplit
  rw [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]; simp [hi]


end AdaptDisintegration
end OSSS
end StatMech
