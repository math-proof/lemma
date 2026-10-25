/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.ConnectiveBounds.Part2


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


lemma zd_sum_stepVec_pos {d : ℕ} (i : Fin d) :
    ∑ j : Fin d, zdStepVec ((i, true) : ZdStep d) j = 1 := by
  unfold zdStepVec; simp


lemma zd_totalSum_wOf {d n : ℕ} (σ : Fin n → Fin d) (k : ℕ) (hk : k ≤ n) :
    ∑ j : Fin d, (zdPos (zdWOf σ) k) j = (k : ℤ) := by
  unfold zdPos zdStepN zdWOf
  simp_rw [Finset.sum_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl
    (fun i hi => by
      have : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
      rw [dif_pos this]
      exact zd_sum_stepVec_pos (σ ⟨i, this⟩))]
  simp


lemma zd_isSAW_wOf {d n : ℕ} (σ : Fin n → Fin d) : ZdIsSAW (zdWOf σ) := by
  intro k1 k2 h1 h2 h
  have : (∑ j : Fin d, (zdPos (zdWOf σ) k1) j) = (∑ j : Fin d, (zdPos (zdWOf σ) k2) j) := by
    rw [h]
  rw [zd_totalSum_wOf σ k1 h1, zd_totalSum_wOf σ k2 h2] at this
  exact_mod_cast this


lemma zd_wOf_injective {d n : ℕ} : Function.Injective (zdWOf : (Fin n → Fin d) → _) := by
  intro σ1 σ2 h
  funext i
  have := congrFun h i
  simp only [zdWOf, Prod.mk.injEq] at this
  exact this.1


theorem zd_pow_le_sawCount {d n : ℕ} : d ^ n ≤ zdSAWCount d n := by
  unfold zdSAWCount
  have himg : (Finset.univ : Finset (Fin n → Fin d)).image zdWOf ⊆ zdSAWWalks d n := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨σ, rfl⟩ := hw
    exact zd_mem_sawWalks.mpr (zd_isSAW_wOf σ)
  calc d ^ n = (Finset.univ : Finset (Fin n → Fin d)).card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ = ((Finset.univ : Finset (Fin n → Fin d)).image zdWOf).card := by
          rw [Finset.card_image_of_injective _ zd_wOf_injective]
    _ ≤ _ := Finset.card_le_card himg


lemma zd_isSAW_isNB {d n : ℕ} {w : Fin n → ZdStep d} (hw : ZdIsSAW w) : ZdIsNB w := by
  intro i h hcon
  set m := (i : ℕ) with hmdef
  have hm1 : m < n := i.2
  have hm2 : m + 1 < n := h
  have step1 : zdPos w (m + 1) = zdPos w m + zdStepN w m := zdPos_succ w m
  have step2 : zdPos w (m + 1 + 1) = zdPos w (m + 1) + zdStepN w (m + 1) := zdPos_succ w (m + 1)
  have hwm : w ⟨m + 1, hm2⟩ = zdReverse (w ⟨m, hm1⟩) := by
    have hc : w ⟨(i : ℕ) + 1, h⟩ = zdReverse (w i) := hcon
    simpa [hmdef] using hc
  have hstepm : zdStepN w m = zdStepVec (w ⟨m, hm1⟩) := by unfold zdStepN; rw [dif_pos hm1]
  have hstepm1 : zdStepN w (m + 1) = zdStepVec (w ⟨m + 1, hm2⟩) := by
    unfold zdStepN; rw [dif_pos hm2]
  have hpe : zdPos w (m + 1 + 1) = zdPos w m := by
    rw [step2, step1, hstepm, hstepm1, hwm, zdStepVec_reverse]; abel
  have heq := hw (m + 1 + 1) m (by omega) (by omega) hpe
  omega


lemma zd_sawWalks_subset_nbWalks {d n : ℕ} : zdSAWWalks d n ⊆ zdNBWalks d n := by
  intro w hw
  exact zd_mem_nbWalks.mpr (zd_isSAW_isNB (zd_mem_sawWalks.mp hw))


end StatMech.Universality
