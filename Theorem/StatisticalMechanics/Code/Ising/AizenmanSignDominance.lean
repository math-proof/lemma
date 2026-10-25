/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanSignDominance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem asd_weight_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (n : Current V) : 0 ≤ Sharpness.weight G β J n := by
  unfold Sharpness.weight
  refine Finset.prod_nonneg (fun e _ => ?_)
  exact div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e)) _) (Nat.cast_nonneg _)


theorem asd_splitWeightedSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (F : ℝ) (hF : 0 ≤ F) (A : Finset V) :
    0 ≤ splitWeightedSum G β J m F A := by
  unfold splitWeightedSum
  refine Finset.sum_nonneg (fun K _ => ?_)
  by_cases h : Sharpness.sources G K.1 = A
  · rw [if_pos h]
    exact mul_nonneg hF (mul_nonneg (asd_weight_nonneg G β J hβ hJ _)
      (asd_weight_nonneg G β J hβ hJ _))
  · rw [if_neg h]

end Ising


namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem asd_switching_weighted_edgecopy (ends : ι → Sym2 V) (m P : Finset ι)
    (hP : P ⊆ m) (A : Finset V) (φ : Finset ι → ℝ)
    (hφ : ∀ K, K ⊆ m → φ (K ∆ P) = φ K) :
    ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ sources ends P), φ K
      = ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K := by
  have hbij := sources_shift_bijOn ends m P hP A
  have himg : (m.powerset.filter (fun K => sources ends K = A ∆ sources ends P))
      = (m.powerset.filter (fun K => sources ends K = A)).image (fun K => K ∆ P) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · intro ⟨hKm, hKsrc⟩
      obtain ⟨L, hL, hLK⟩ := hbij.2.2 ⟨hKm, hKsrc⟩
      exact ⟨L, ⟨hL.1, hL.2⟩, hLK⟩
    · rintro ⟨L, ⟨hLm, hLsrc⟩, rfl⟩
      have := hbij.1 ⟨hLm, hLsrc⟩
      exact ⟨this.1, this.2⟩
  rw [himg, Finset.sum_image]
  · exact Finset.sum_congr rfl (fun K hK => by
      simp only [Finset.mem_filter, Finset.mem_powerset] at hK; exact hφ K hK.1)
  · intro K₁ hK₁ K₂ hK₂ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hK₁ hK₂
    exact hbij.2.1 ⟨hK₁.1, hK₁.2⟩ ⟨hK₂.1, hK₂.2⟩ h


theorem asd_switching_weighted_indicator (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), φ K
      = (if connK ends m u v then 1 else 0) *
          ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K := by
  by_cases hconn : connK ends m u v
  · rw [if_pos hconn, one_mul]
    obtain ⟨P, hPm, hPsrc⟩ := exists_conn_set ends m hconn huv
    have := asd_switching_weighted_edgecopy ends m P hPm A φ (fun K hK => hφ K P hPm hK)
    rwa [hPsrc] at this
  · rw [if_neg hconn, zero_mul]
    refine Finset.sum_eq_zero (fun K hK => ?_)
    exfalso
    simp only [Finset.mem_filter, Finset.mem_powerset] at hK
    obtain ⟨hKm, hKsrc⟩ := hK
    
    set L := m \ K with hL
    have hLm : L ⊆ m := Finset.sdiff_subset
    have hLeq : L = m ∆ K := by
      rw [hL]; ext x
      simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
      constructor
      · rintro ⟨hm0, hk⟩; left; exact ⟨hm0, hk⟩
      · rintro (⟨hm0, hk⟩ | ⟨hk, hm0⟩)
        · exact ⟨hm0, hk⟩
        · exact absurd (hKm hk) hm0
    have hLsrc : sources ends L = {u, v} := by
      rw [hLeq, sources_symmDiff, hm, hKsrc, ← symmDiff_assoc, symmDiff_self, bot_symmDiff]
    have hu_odd : Odd (degK ends L u) := by rw [← mem_sources, hLsrc]; simp
    have hbdry : ∀ x, Odd (degK ends L x) → x = u ∨ x = v := by
      intro x hx; rw [← mem_sources, hLsrc] at hx; simpa using hx
    have hconnL : connK ends L u v :=
      path_exists ends L (fun i hi => hnd i (hLm hi)) u v hu_odd hbdry huv
    have hmono : connK ends m u v :=
      Relation.ReflTransGen.mono
        (fun a b ⟨i, hi, ha, hb, hne⟩ => ⟨i, hLm hi, ha, hb, hne⟩) _ _ hconnL
    exact hconn hmono


theorem asd_signDominance_edgecopy (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), φ K
      ≤ ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K := by
  rw [asd_switching_weighted_indicator ends m hnd A hm huv φ hφ]
  set S := ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun K _ => hφnn K)
  by_cases hconn : connK ends m u v
  · rw [if_pos hconn, one_mul]
  · rw [if_neg hconn, zero_mul]; exact hSnn


theorem asd_signDominance (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) (w : Finset ι → ℝ)
    (hwnn : ∀ K, 0 ≤ w K) (hw : ∀ K P, P ⊆ m → K ⊆ m → w (K ∆ P) = w K) :
    ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), w K
      ≤ ∑ K ∈ m.powerset.filter (fun K => sources ends K = A), w K :=
  asd_signDominance_edgecopy ends m hnd A hm huv w hwnn hw


theorem asd_signedSplit_nonneg_edgecopy (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    0 ≤ (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K)
          - ∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), φ K := by
  have h := asd_signDominance_edgecopy ends m hnd A hm huv φ hφnn hφ
  linarith


theorem asd_ghsSigned_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K)
      - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {x, y}), φ K)
      - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, y}), φ K)
      - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, x}), φ K)
      = (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) *
          (1 - (if connK ends m x y then 1 else 0)
             - (if connK ends m o y then 1 else 0)
             - (if connK ends m o x then 1 else 0)) := by
  rw [asd_switching_weighted_indicator ends m hnd A hm hxy φ hφ,
      asd_switching_weighted_indicator ends m hnd A hm hoy φ hφ,
      asd_switching_weighted_indicator ends m hnd A hm hox φ hφ]
  ring


end RandomCurrent
end Sharpness
end StatMech
