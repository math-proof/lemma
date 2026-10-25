/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Def.StatisticalMechanics.Code.Walls.vbgtriangle.Part2
open scoped BigOperators
open Finset


namespace StatMech

namespace Walls

namespace VBG

set_option linter.unusedSectionVars false

set_option linter.style.longLine false

set_option maxHeartbeats 800000


variable {Ω : Type*} [Fintype Ω]


section Prop1

variable (μ : Ω → ℝ) (X Y Z : Ω → ℝ)


section CondFKG

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem vbg_coordUp_idem (j : E) (ω : ConfigSpace E) :
    vbg_coordUp j ω * vbg_coordUp j ω = vbg_coordUp j ω := by
  unfold vbg_coordUp; by_cases h : ω j <;> simp [h]


theorem vbg_coordDown_idem (j : E) (ω : ConfigSpace E) :
    vbg_coordDown j ω * vbg_coordDown j ω = vbg_coordDown j ω := by
  unfold vbg_coordDown; by_cases h : ω j <;> simp [h]


theorem vbg_sup_apply (ω ω' : ConfigSpace E) (e : E) : (ω ⊔ ω') e = (ω e || ω' e) := rfl

theorem vbg_inf_apply (ω ω' : ConfigSpace E) (e : E) : (ω ⊓ ω') e = (ω e && ω' e) := rfl


theorem vbg_coordUp_logSupermod (j : E) (ω ω' : ConfigSpace E) :
    vbg_coordUp j ω * vbg_coordUp j ω'
      ≤ vbg_coordUp j (ω ⊔ ω') * vbg_coordUp j (ω ⊓ ω') := by
  unfold vbg_coordUp
  rw [vbg_sup_apply, vbg_inf_apply]
  by_cases h : ω j <;> by_cases h' : ω' j <;> simp [h, h']


theorem vbg_coordDown_logSupermod (j : E) (ω ω' : ConfigSpace E) :
    vbg_coordDown j ω * vbg_coordDown j ω'
      ≤ vbg_coordDown j (ω ⊔ ω') * vbg_coordDown j (ω ⊓ ω') := by
  unfold vbg_coordDown
  rw [vbg_sup_apply, vbg_inf_apply]
  by_cases h : ω j <;> by_cases h' : ω' j <;> simp [h, h']


theorem vbg_mul_logSupermod {π Y : ConfigSpace E → ℝ} (hπ0 : 0 ≤ π) (hY0 : 0 ≤ Y)
    (hπ : FKGLatticeCondition π)
    (hY : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω')) :
    FKGLatticeCondition (fun ω => π ω * Y ω) := by
  intro ω ω'
  have hππ := hπ ω ω'
  have hYY := hY ω ω'
  
  have e1 : π ω * Y ω * (π ω' * Y ω') = (π ω * π ω') * (Y ω * Y ω') := by ring
  have e2 : π (ω ⊔ ω') * Y (ω ⊔ ω') * (π (ω ⊓ ω') * Y (ω ⊓ ω'))
      = (π (ω ⊔ ω') * π (ω ⊓ ω')) * (Y (ω ⊔ ω') * Y (ω ⊓ ω')) := by ring
  rw [e1, e2]
  apply mul_le_mul hππ hYY
  · exact mul_nonneg (hY0 _) (hY0 _)
  · exact mul_nonneg (hπ0 _) (hπ0 _)


theorem vbg_div_const_logSupermod {ρ : ConfigSpace E → ℝ} (c : ℝ) (hc : 0 < c)
    (hρ : FKGLatticeCondition ρ) : FKGLatticeCondition (fun ω => ρ ω / c) := by
  intro ω ω'
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right (hρ ω ω') (by positivity)


theorem vbg_condPlus_FKG {π Y : ConfigSpace E → ℝ} (hπ0 : 0 ≤ π) (hY0 : 0 ≤ Y)
    (hπ : FKGLatticeCondition π)
    (hY : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω'))
    (hp0 : 0 < vbg_exp π Y) : FKGLatticeCondition (vbg_condPlus π Y) := by
  have hmul : FKGLatticeCondition (fun ω => π ω * Y ω) := vbg_mul_logSupermod hπ0 hY0 hπ hY
  have := vbg_div_const_logSupermod (vbg_exp π Y) hp0 hmul
  convert this using 1


theorem vbg_covPlus_nonneg {π Y f g : ConfigSpace E → ℝ} (hπ0 : 0 ≤ π) (hY0 : 0 ≤ Y)
    (hπ : FKGLatticeCondition π)
    (hY : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω'))
    (hp0 : 0 < vbg_exp π Y) (hf : Monotone f) (hg : Monotone g) :
    0 ≤ vbg_covPlus π Y f g := by
  unfold vbg_covPlus vbg_cov
  have hfkg := fkg_inequality (vbg_condPlus_nonneg hπ0 hY0 hp0) (vbg_condPlus_norm hp0)
    (vbg_condPlus_FKG hπ0 hY0 hπ hY hp0) hf hg
  
  have e : vbg_exp (vbg_condPlus π Y) (fun ω => f ω * g ω)
      = ∑ ω, vbg_condPlus π Y ω * (f ω * g ω) := rfl
  have e2 : ∀ h', vbg_exp (vbg_condPlus π Y) h' = ∑ ω, vbg_condPlus π Y ω * h' ω := fun _ => rfl
  rw [e2, e2, e2]
  linarith [hfkg]


theorem vbg_covMinus_nonneg {π Y f g : ConfigSpace E → ℝ} (hπ0 : 0 ≤ π) (hπnorm : ∑ ω, π ω = 1)
    (hYbnd : ∀ ω, Y ω ≤ 1)
    (hπ : FKGLatticeCondition π)
    (hYc : ∀ ω ω', (1 - Y ω) * (1 - Y ω') ≤ (1 - Y (ω ⊔ ω')) * (1 - Y (ω ⊓ ω')))
    (hp1 : vbg_exp π Y < 1) (hf : Monotone f) (hg : Monotone g) :
    0 ≤ vbg_covMinus π Y f g := by
  have hcompl0 : (0 : ConfigSpace E → ℝ) ≤ (fun ω => 1 - Y ω) := by
    intro ω; show (0 : ℝ) ≤ 1 - Y ω; linarith [hYbnd ω]
  have hp0' : 0 < vbg_exp π (fun ω => 1 - Y ω) := by
    rw [vbg_exp_one_sub hπnorm]; linarith
  have h := vbg_covPlus_nonneg (Y := fun ω => 1 - Y ω) (f := f) (g := g)
    hπ0 hcompl0 hπ hYc hp0' hf hg
  unfold vbg_covMinus vbg_covPlus at *
  rw [vbg_condMinus_eq_condPlus hπnorm]
  exact h


theorem vbg_thm1_configSpace {π : ConfigSpace E → ℝ} (hπ0 : 0 ≤ π) (hπnorm : ∑ ω, π ω = 1)
    (hπ : FKGLatticeCondition π) (j : E) {X Z : ConfigSpace E → ℝ}
    (hX : Monotone X) (hZ : Monotone Z)
    (hp0 : 0 < vbg_exp π (vbg_coordUp j)) (hp1 : vbg_exp π (vbg_coordUp j) < 1) :
    vbg_cov π X (vbg_coordUp j) * vbg_cov π (vbg_coordUp j) Z
      ≤ vbg_var π (vbg_coordUp j) * vbg_cov π X Z := by
  set Y := vbg_coordUp j with hYdef
  have hYidem : ∀ ω, Y ω * Y ω = Y ω := fun ω => vbg_coordUp_idem j ω
  have hY0 : (0 : ConfigSpace E → ℝ) ≤ Y := by
    intro ω; show (0:ℝ) ≤ vbg_coordUp j ω; unfold vbg_coordUp; by_cases h : ω j <;> simp [h]
  have hYbnd : ∀ ω, Y ω ≤ 1 := by
    intro ω; show vbg_coordUp j ω ≤ 1; unfold vbg_coordUp; by_cases h : ω j <;> simp [h]
  have hYls : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω') := vbg_coordUp_logSupermod j
  
  have hcompleq : ∀ ω, 1 - Y ω = vbg_coordDown j ω := by
    intro ω; show 1 - vbg_coordUp j ω = vbg_coordDown j ω
    unfold vbg_coordUp vbg_coordDown; by_cases h : ω j <;> simp [h]
  have hYc : ∀ ω ω', (1 - Y ω) * (1 - Y ω') ≤ (1 - Y (ω ⊔ ω')) * (1 - Y (ω ⊓ ω')) := by
    intro ω ω'; rw [hcompleq, hcompleq, hcompleq, hcompleq]; exact vbg_coordDown_logSupermod j ω ω'
  
  have hCovP : 0 ≤ vbg_covPlus π Y X Z := vbg_covPlus_nonneg hπ0 hY0 hπ hYls hp0 hX hZ
  have hCovM : 0 ≤ vbg_covMinus π Y X Z := vbg_covMinus_nonneg hπ0 hπnorm hYbnd hπ hYc hp1 hX hZ
  
  set LHS2 := vbg_exp π Y * vbg_varPlus π Y X + (1 - vbg_exp π Y) * vbg_varMinus π Y X with hL2
  have hVP0 : 0 ≤ vbg_varPlus π Y X := by
    unfold vbg_varPlus
    exact vbg_var_nonneg _ (vbg_condPlus_nonneg hπ0 hY0 hp0) (vbg_condPlus_norm hp0) X
  have hVM0 : 0 ≤ vbg_varMinus π Y X := by
    unfold vbg_varMinus
    have hq0 : 0 < vbg_exp π (fun ω => 1 - Y ω) := by rw [vbg_exp_one_sub hπnorm]; linarith
    rw [vbg_condMinus_eq_condPlus hπnorm]
    exact vbg_var_nonneg _ (vbg_condPlus_nonneg hπ0 (by intro ω; show (0:ℝ) ≤ 1 - Y ω; linarith [hYbnd ω]) hq0)
      (vbg_condPlus_norm hq0) X
  have hL2nn : 0 ≤ LHS2 := by
    rw [hL2]; exact add_nonneg (mul_nonneg hp0.le hVP0) (mul_nonneg (by linarith) hVM0)
  rcases eq_or_lt_of_le hL2nn with hL2eq | hL2pos
  · 
    have hVPz : vbg_varPlus π Y X = 0 := by
      by_contra hne
      have : 0 < vbg_exp π Y * vbg_varPlus π Y X := mul_pos hp0 (lt_of_le_of_ne hVP0 (Ne.symm hne))
      have := mul_nonneg (show (0:ℝ) ≤ 1 - vbg_exp π Y by linarith) hVM0
      linarith [hL2eq]
    have hVMz : vbg_varMinus π Y X = 0 := by
      by_contra hne
      have h1 : 0 < (1 - vbg_exp π Y) * vbg_varMinus π Y X :=
        mul_pos (by linarith) (lt_of_le_of_ne hVM0 (Ne.symm hne))
      have := mul_nonneg hp0.le hVP0
      linarith [hL2eq]
    have := vbg_thm1_degenerate π X Y Z hπ0 hπnorm hYidem hp0 hp1 hVPz hVMz
    linarith [this]
  · 
    exact vbg_thm1 π X Y Z hπ0 hπnorm hYidem hp0 hp1 hCovP hCovM (by rw [← hL2]; exact hL2pos)

end CondFKG

end Prop1


section Ising

open StatMech.Ising StatMech.ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem vbg_isingExp_eq (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h f = vbg_exp (isingProb G β h) f := rfl


theorem vbg_cov2_eq (β h : ℝ) (x y : V) :
    cov2 G β h x y = vbg_cov (isingProb G β h) (fun s => spin s x) (fun s => spin s y) := by
  unfold cov2 vbg_cov vbg_exp isingExpectation; rfl


theorem vbg_spin_eq_coordUp (j : V) (s : ConfigSpace V) :
    spin s j = 2 * vbg_coordUp j s - 1 := by
  unfold spin vbg_coordUp
  by_cases h : s j <;> · simp only [h, Bool.false_eq_true, if_true, if_false]; ring


theorem vbg_spin_monotone (j : V) : Monotone (fun s : ConfigSpace V => spin s j) :=
  fun _ _ hab => StatMech.Ising.ifk_spin_mono hab j


theorem vbg_cov_affine_right (μ : ConfigSpace V → ℝ) (hμ : ∑ ω, μ ω = 1) (f g : ConfigSpace V → ℝ)
    (a b : ℝ) : vbg_cov μ f (fun ω => a * g ω + b) = a * vbg_cov μ f g := by
  unfold vbg_cov vbg_exp
  have e1 : (∑ ω, μ ω * (f ω * (a * g ω + b)))
      = a * (∑ ω, μ ω * (f ω * g ω)) + b * ∑ ω, μ ω * f ω := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have e2 : (∑ ω, μ ω * (a * g ω + b)) = a * (∑ ω, μ ω * g ω) + b * ∑ ω, μ ω := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [e1, e2, hμ]; ring

theorem vbg_cov_affine_left (μ : ConfigSpace V → ℝ) (hμ : ∑ ω, μ ω = 1) (f g : ConfigSpace V → ℝ)
    (a b : ℝ) : vbg_cov μ (fun ω => a * f ω + b) g = a * vbg_cov μ f g := by
  unfold vbg_cov vbg_exp
  have e1 : (∑ ω, μ ω * ((a * f ω + b) * g ω))
      = a * (∑ ω, μ ω * (f ω * g ω)) + b * ∑ ω, μ ω * g ω := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have e2 : (∑ ω, μ ω * (a * f ω + b)) = a * (∑ ω, μ ω * f ω) + b * ∑ ω, μ ω := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [e1, e2, hμ]; ring


theorem vbg_cov_spin_coordUp (β h : ℝ) (x j : V) :
    vbg_cov (isingProb G β h) (fun s => spin s x) (fun s => spin s j)
      = 2 * vbg_cov (isingProb G β h) (fun s => spin s x) (vbg_coordUp j) := by
  have hnorm : ∑ ω, isingProb G β h ω = 1 := isingProb_sum_eq_one G β h
  have : (fun s => spin s j) = (fun s => 2 * vbg_coordUp j s + (-1)) := by
    funext s; rw [vbg_spin_eq_coordUp]; ring
  rw [this, vbg_cov_affine_right (isingProb G β h) hnorm _ (vbg_coordUp j) 2 (-1)]


theorem vbg_ising_coordUp_pos_lt_one (β h : ℝ) (j : V) :
    0 < vbg_exp (isingProb G β h) (vbg_coordUp j)
      ∧ vbg_exp (isingProb G β h) (vbg_coordUp j) < 1 := by
  
  have hexpand : vbg_exp (isingProb G β h) (vbg_coordUp j)
      = ∑ s, isingProb G β h s * vbg_coordUp j s := rfl
  
  set sT : ConfigSpace V := fun i => if i = j then true else false with hsT
  set sF : ConfigSpace V := fun i => false with hsF
  have hYnn : ∀ s, 0 ≤ isingProb G β h s * vbg_coordUp j s := by
    intro s; apply mul_nonneg (isingProb_nonneg G β h s)
    unfold vbg_coordUp; by_cases hh : s j <;> simp [hh]
  have hYle : ∀ s, isingProb G β h s * vbg_coordUp j s ≤ isingProb G β h s := by
    intro s; unfold vbg_coordUp
    by_cases hh : s j <;> simp [hh, (isingProb_nonneg G β h s)]
  constructor
  · 
    rw [hexpand]
    exact Finset.sum_pos' (fun s _ => hYnn s) ⟨sT, Finset.mem_univ sT, by
      have hpos := isingProb_pos G β h sT
      have : vbg_coordUp j sT = 1 := by unfold vbg_coordUp; rw [hsT]; simp
      rw [this, mul_one]; exact hpos⟩
  · 
    have hsum1 : ∑ s, isingProb G β h s = 1 := isingProb_sum_eq_one G β h
    rw [hexpand]
    have hlt : ∑ s, isingProb G β h s * vbg_coordUp j s < ∑ s, isingProb G β h s := by
      apply Finset.sum_lt_sum (fun s _ => hYle s) ⟨sF, Finset.mem_univ sF, ?_⟩
      have hpos := isingProb_pos G β h sF
      have : vbg_coordUp j sF = 0 := by unfold vbg_coordUp; rw [hsF]; simp
      rw [this, mul_zero]; exact hpos
    rw [hsum1] at hlt; exact hlt


theorem vbg_cor1 (β h : ℝ) (hβ : 0 ≤ β) (i j k : V) :
    cov2 G β h i j * cov2 G β h j k
      ≤ vbg_var (isingProb G β h) (fun s => spin s j) * cov2 G β h i k := by
  have hπ0 : (0 : ConfigSpace V → ℝ) ≤ isingProb G β h := fun s => isingProb_nonneg G β h s
  have hπnorm : ∑ ω, isingProb G β h ω = 1 := isingProb_sum_eq_one G β h
  have hπfkg : FKGLatticeCondition (fun s => isingProb G β h s) :=
    StatMech.Ising.ifk_isingProb_FKGLatticeCondition G hβ h
  obtain ⟨hp0, hp1⟩ := vbg_ising_coordUp_pos_lt_one G β h j
  
  have hT1 := vbg_thm1_configSpace hπ0 hπnorm hπfkg j
    (X := fun s => spin s i) (Z := fun s => spin s k)
    (vbg_spin_monotone i) (vbg_spin_monotone k) hp0 hp1
  
  
  have hij : cov2 G β h i j = 2 * vbg_cov (isingProb G β h) (fun s => spin s i) (vbg_coordUp j) := by
    rw [vbg_cov2_eq]; exact vbg_cov_spin_coordUp G β h i j
  have hjk : cov2 G β h j k = 2 * vbg_cov (isingProb G β h) (vbg_coordUp j) (fun s => spin s k) := by
    rw [vbg_cov2_eq]
    
    have heq : (fun s => spin s j) = (fun s => 2 * vbg_coordUp j s + (-1)) := by
      funext s; rw [vbg_spin_eq_coordUp]; ring
    rw [heq, vbg_cov_affine_left (isingProb G β h) hπnorm (vbg_coordUp j) (fun s => spin s k) 2 (-1)]
  have hik : cov2 G β h i k
      = vbg_cov (isingProb G β h) (fun s => spin s i) (fun s => spin s k) := vbg_cov2_eq G β h i k
  
  have hvarj : vbg_var (isingProb G β h) (fun s => spin s j)
      = 4 * vbg_var (isingProb G β h) (vbg_coordUp j) := by
    unfold vbg_var
    have heq : (fun s => spin s j) = (fun s => 2 * vbg_coordUp j s + (-1)) := by
      funext s; rw [vbg_spin_eq_coordUp]; ring
    rw [heq, vbg_cov_affine_left (isingProb G β h) hπnorm (vbg_coordUp j) _ 2 (-1),
      vbg_cov_affine_right (isingProb G β h) hπnorm _ (vbg_coordUp j) 2 (-1)]
    ring
  rw [hij, hjk, hik, hvarj]
  
  nlinarith [hT1]

end Ising
end VBG
end Walls
end StatMech
