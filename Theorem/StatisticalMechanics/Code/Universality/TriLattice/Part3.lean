/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.TriLattice.Part3


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


lemma tri_phi_pos_wOf {n : ℕ} (σ : Fin n → Fin 3) (k : ℕ) (hk : k ≤ n) :
    (k : ℤ) ≤ triPhi (triPos (triWOf σ) k) := by
  induction k with
  | zero => simp [triPos, triPhi_zero]
  | succ j ih =>
    have hj : j ≤ n := by omega
    have hjn : j < n := by omega
    have hstep : triStepN (triWOf σ) j = triStepVec (triPosStep (σ ⟨j, hjn⟩)) := by
      unfold triStepN triWOf; rw [dif_pos hjn]
    rw [triPos_succ, triPhi_add, hstep]
    have h1 := tri_phi_posStep (σ ⟨j, hjn⟩)
    have h2 := ih hj
    push_cast
    linarith


lemma tri_phi_pos_strictMono {n : ℕ} (σ : Fin n → Fin 3) {k1 k2 : ℕ}
    (h12 : k1 < k2) (hk2 : k2 ≤ n) :
    triPhi (triPos (triWOf σ) k1) < triPhi (triPos (triWOf σ) k2) := by
  
  
  induction k2 with
  | zero => omega
  | succ j ih =>
    have hjn : j < n := by omega
    have hstep : triStepN (triWOf σ) j = triStepVec (triPosStep (σ ⟨j, hjn⟩)) := by
      unfold triStepN triWOf; rw [dif_pos hjn]
    have hpos : 1 ≤ triPhi (triStepVec (triPosStep (σ ⟨j, hjn⟩))) := tri_phi_posStep _
    rw [triPos_succ, triPhi_add, hstep]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h12 with hlt | heq
    · have := ih hlt (by omega)
      linarith
    · subst heq
      linarith


lemma tri_isSAW_wOf {n : ℕ} (σ : Fin n → Fin 3) : TriIsSAW (triWOf σ) := by
  intro k1 k2 h1 h2 h
  by_contra hne
  rcases Nat.lt_or_ge k1 k2 with hlt | hge
  · have := tri_phi_pos_strictMono σ hlt h2
    rw [h] at this; exact lt_irrefl _ this
  · have hlt : k2 < k1 := lt_of_le_of_ne hge (by omega)
    have := tri_phi_pos_strictMono σ hlt h1
    rw [h] at this; exact lt_irrefl _ this


lemma tri_posStep_injective : Function.Injective triPosStep := by
  decide


lemma tri_wOf_injective {n : ℕ} : Function.Injective (triWOf : (Fin n → Fin 3) → _) := by
  intro σ1 σ2 h
  funext i
  have := congrFun h i
  simp only [triWOf] at this
  exact tri_posStep_injective this


theorem tri_pow_le_sawCount {n : ℕ} : 3 ^ n ≤ triSAWCount n := by
  unfold triSAWCount
  have himg : (Finset.univ : Finset (Fin n → Fin 3)).image triWOf ⊆ triSAWWalks n := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨σ, rfl⟩ := hw
    exact tri_mem_sawWalks.mpr (tri_isSAW_wOf σ)
  calc 3 ^ n = (Finset.univ : Finset (Fin n → Fin 3)).card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ = ((Finset.univ : Finset (Fin n → Fin 3)).image triWOf).card := by
          rw [Finset.card_image_of_injective _ tri_wOf_injective]
    _ ≤ _ := Finset.card_le_card himg


lemma tri_isSAW_isNB {n : ℕ} {w : Fin n → TriStep} (hw : TriIsSAW w) : TriIsNB w := by
  intro i h hcon
  set m := (i : ℕ) with hmdef
  have hm1 : m < n := i.2
  have hm2 : m + 1 < n := h
  have step1 : triPos w (m + 1) = triPos w m + triStepN w m := triPos_succ w m
  have step2 : triPos w (m + 1 + 1) = triPos w (m + 1) + triStepN w (m + 1) :=
    triPos_succ w (m + 1)
  have hwm : w ⟨m + 1, hm2⟩ = triReverse (w ⟨m, hm1⟩) := by
    have hc : w ⟨(i : ℕ) + 1, h⟩ = triReverse (w i) := hcon
    simpa [hmdef] using hc
  have hstepm : triStepN w m = triStepVec (w ⟨m, hm1⟩) := by
    unfold triStepN; rw [dif_pos hm1]
  have hstepm1 : triStepN w (m + 1) = triStepVec (w ⟨m + 1, hm2⟩) := by
    unfold triStepN; rw [dif_pos hm2]
  have hpe : triPos w (m + 1 + 1) = triPos w m := by
    rw [step2, step1, hstepm, hstepm1, hwm, triStepVec_reverse]; abel
  have heq := hw (m + 1 + 1) m (by omega) (by omega) hpe
  omega


lemma tri_sawWalks_subset_nbWalks {n : ℕ} : triSAWWalks n ⊆ triNBWalks n := by
  intro w hw
  exact tri_mem_nbWalks.mpr (tri_isSAW_isNB (tri_mem_sawWalks.mp hw))


end StatMech.Universality
