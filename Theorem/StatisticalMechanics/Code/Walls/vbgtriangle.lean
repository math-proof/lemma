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
import Def.StatisticalMechanics.Code.Walls.vbgtriangle
open scoped BigOperators
open Finset


namespace StatMech

namespace Walls

namespace VBG

set_option linter.unusedSectionVars false

set_option linter.style.longLine false

set_option maxHeartbeats 800000


variable {Ω : Type*} [Fintype Ω]


theorem vbg_exp_add (μ : Ω → ℝ) (f g : Ω → ℝ) :
    vbg_exp μ (fun ω => f ω + g ω) = vbg_exp μ f + vbg_exp μ g := by
  unfold vbg_exp; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun ω _ => by ring)

theorem vbg_exp_const_mul (μ : Ω → ℝ) (c : ℝ) (f : Ω → ℝ) :
    vbg_exp μ (fun ω => c * f ω) = c * vbg_exp μ f := by
  unfold vbg_exp; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)


theorem vbg_exp_reweight (μ w : Ω → ℝ) (c : ℝ) (f : Ω → ℝ) :
    vbg_exp (fun ω => μ ω * w ω / c) f = (∑ ω, μ ω * w ω * f ω) / c := by
  unfold vbg_exp
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


section Prop1

variable (μ : Ω → ℝ) (X Y Z : Ω → ℝ)


theorem vbg_expPlus_eq (f : Ω → ℝ) :
    vbg_exp (vbg_condPlus μ Y) f = (∑ ω, μ ω * Y ω * f ω) / vbg_exp μ Y := by
  unfold vbg_condPlus
  exact vbg_exp_reweight μ Y (vbg_exp μ Y) f


theorem vbg_expMinus_eq (f : Ω → ℝ) :
    vbg_exp (vbg_condMinus μ Y) f = (∑ ω, μ ω * (1 - Y ω) * f ω) / (1 - vbg_exp μ Y) := by
  unfold vbg_condMinus
  exact vbg_exp_reweight μ (fun ω => 1 - Y ω) (1 - vbg_exp μ Y) f


theorem vbg_prop1 (hY : ∀ ω, Y ω * Y ω = Y ω)
    (hp0 : 0 < vbg_exp μ Y) (hp1 : vbg_exp μ Y < 1) :
    (vbg_var μ Y * vbg_cov μ X Z - vbg_cov μ X Y * vbg_cov μ Y Z)
        * (vbg_exp μ Y * vbg_varPlus μ Y X + (1 - vbg_exp μ Y) * vbg_varMinus μ Y X)
      = (vbg_exp μ Y * vbg_covPlus μ Y X Z + (1 - vbg_exp μ Y) * vbg_covMinus μ Y X Z)
        * (vbg_var μ X * vbg_var μ Y - vbg_cov μ X Y ^ 2) := by
  
  set p := vbg_exp μ Y with hp
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have hq_ne : (1 - p) ≠ 0 := by intro h; apply absurd hp1; linarith [sub_eq_zero.mp h]
  
  simp only [vbg_varPlus, vbg_varMinus, vbg_covPlus, vbg_covMinus, vbg_var, vbg_cov,
    vbg_expPlus_eq, vbg_expMinus_eq, ← hp]
  
  set AX := ∑ ω, μ ω * Y ω * X ω with hAX
  set AZ := ∑ ω, μ ω * Y ω * Z ω with hAZ
  set AXZ := ∑ ω, μ ω * Y ω * (X ω * Z ω) with hAXZ
  set AXX := ∑ ω, μ ω * Y ω * (X ω * X ω) with hAXX
  set BX := ∑ ω, μ ω * (1 - Y ω) * X ω with hBX
  set BZ := ∑ ω, μ ω * (1 - Y ω) * Z ω with hBZ
  set BXZ := ∑ ω, μ ω * (1 - Y ω) * (X ω * Z ω) with hBXZ
  set BXX := ∑ ω, μ ω * (1 - Y ω) * (X ω * X ω) with hBXX
  
  
  
  have eEX : vbg_exp μ X = AX + BX := by
    rw [hAX, hBX]; unfold vbg_exp; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have eEZ : vbg_exp μ Z = AZ + BZ := by
    rw [hAZ, hBZ]; unfold vbg_exp; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have eEXZ : vbg_exp μ (fun ω => X ω * Z ω) = AXZ + BXZ := by
    rw [hAXZ, hBXZ]; unfold vbg_exp; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have eEXX : vbg_exp μ (fun ω => X ω * X ω) = AXX + BXX := by
    rw [hAXX, hBXX]; unfold vbg_exp; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have eEYY : vbg_exp μ (fun ω => Y ω * Y ω) = p := by
    rw [hp]; unfold vbg_exp
    exact Finset.sum_congr rfl (fun ω _ => by simp only []; rw [hY ω])
  have eEXY : vbg_exp μ (fun ω => X ω * Y ω) = AX := by
    rw [hAX]; unfold vbg_exp; exact Finset.sum_congr rfl (fun ω _ => by simp only []; ring)
  have eEYZ : vbg_exp μ (fun ω => Y ω * Z ω) = AZ := by
    rw [hAZ]; unfold vbg_exp; exact Finset.sum_congr rfl (fun ω _ => by simp only []; ring)
  
  rw [eEX, eEZ, eEXZ, eEXX, eEYY, eEXY, eEYZ]
  field_simp
  ring


theorem vbg_cov_centered (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1) (f g : Ω → ℝ) :
    vbg_cov μ f g = ∑ ω, μ ω * ((f ω - vbg_exp μ f) * (g ω - vbg_exp μ g)) := by
  unfold vbg_cov vbg_exp
  have hexp : ∀ (c : ℝ) (φ : Ω → ℝ), (∑ ω, μ ω * (c * φ ω)) = c * ∑ ω, μ ω * φ ω := by
    intro c φ; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)
  have expand : ∀ ω, μ ω * ((f ω - (∑ ω', μ ω' * f ω')) * (g ω - (∑ ω', μ ω' * g ω')))
      = μ ω * (f ω * g ω)
        - (∑ ω', μ ω' * g ω') * (μ ω * f ω)
        - (∑ ω', μ ω' * f ω') * (μ ω * g ω)
        + ((∑ ω', μ ω' * f ω') * (∑ ω', μ ω' * g ω')) * μ ω := fun ω => by ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hμ, mul_one]
  ring


theorem vbg_var_nonneg (μ : Ω → ℝ) (hμ0 : 0 ≤ μ) (hμ : ∑ ω, μ ω = 1) (f : Ω → ℝ) :
    0 ≤ vbg_var μ f := by
  unfold vbg_var
  rw [vbg_cov_centered μ hμ]
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (hμ0 ω) (mul_self_nonneg _)


theorem vbg_cauchy_schwarz (μ : Ω → ℝ) (hμ0 : 0 ≤ μ) (hμ : ∑ ω, μ ω = 1) (f g : Ω → ℝ) :
    vbg_cov μ f g ^ 2 ≤ vbg_var μ f * vbg_var μ g := by
  set a : Ω → ℝ := fun ω => f ω - vbg_exp μ f with ha
  set b : Ω → ℝ := fun ω => g ω - vbg_exp μ g with hb
  have hcov : vbg_cov μ f g = ∑ ω, μ ω * a ω * b ω := by
    rw [vbg_cov_centered μ hμ]; exact Finset.sum_congr rfl (fun ω _ => by rw [ha, hb]; ring)
  have hvf : vbg_var μ f = ∑ ω, μ ω * a ω ^ 2 := by
    unfold vbg_var; rw [vbg_cov_centered μ hμ]
    exact Finset.sum_congr rfl (fun ω _ => by rw [ha]; ring)
  have hvg : vbg_var μ g = ∑ ω, μ ω * b ω ^ 2 := by
    unfold vbg_var; rw [vbg_cov_centered μ hμ]
    exact Finset.sum_congr rfl (fun ω _ => by rw [hb]; ring)
  rw [hcov, hvf, hvg]
  
  have key : (∑ ω, μ ω * a ω * b ω) ^ 2
      ≤ (∑ ω, μ ω * a ω ^ 2) * (∑ ω, μ ω * b ω ^ 2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ)
      (f := fun ω => μ ω * a ω ^ 2) (g := fun ω => μ ω * b ω ^ 2)
      (r := fun ω => μ ω * a ω * b ω)
    · intro ω _; exact mul_nonneg (hμ0 ω) (sq_nonneg _)
    · intro ω _; exact mul_nonneg (hμ0 ω) (sq_nonneg _)
    · intro ω _; nlinarith [sq_nonneg (a ω), sq_nonneg (b ω), hμ0 ω]
  exact key


theorem vbg_condPlus_nonneg {π Y : Ω → ℝ} (hπ0 : 0 ≤ π) (hY0 : 0 ≤ Y)
    (hp0 : 0 < vbg_exp π Y) : 0 ≤ vbg_condPlus π Y := by
  intro ω
  unfold vbg_condPlus
  exact div_nonneg (mul_nonneg (hπ0 ω) (hY0 ω)) hp0.le


theorem vbg_condPlus_norm {π Y : Ω → ℝ} (hp0 : 0 < vbg_exp π Y) :
    ∑ ω, vbg_condPlus π Y ω = 1 := by
  unfold vbg_condPlus
  rw [← Finset.sum_div, div_eq_one_iff_eq (ne_of_gt hp0)]
  unfold vbg_exp
  exact Finset.sum_congr rfl (fun ω _ => by ring)


theorem vbg_exp_one_sub {π Y : Ω → ℝ} (hπ : ∑ ω, π ω = 1) :
    vbg_exp π (fun ω => 1 - Y ω) = 1 - vbg_exp π Y := by
  unfold vbg_exp
  rw [show (∑ ω, π ω * (1 - Y ω)) = (∑ ω, π ω) - ∑ ω, π ω * Y ω by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun ω _ => by ring), hπ]


theorem vbg_condMinus_eq_condPlus {π Y : Ω → ℝ} (hπ : ∑ ω, π ω = 1) :
    vbg_condMinus π Y = vbg_condPlus π (fun ω => 1 - Y ω) := by
  funext ω
  unfold vbg_condMinus vbg_condPlus
  rw [vbg_exp_one_sub hπ]


section Degenerate

variable (μ : Ω → ℝ) (X Y Z : Ω → ℝ)


theorem vbg_ae_const_of_var_zero (hμ0 : 0 ≤ μ) (hμ : ∑ ω, μ ω = 1) (f : Ω → ℝ)
    (hvar : vbg_var μ f = 0) : ∀ ω, μ ω * (f ω - vbg_exp μ f) = 0 := by
  
  have hsum : ∑ ω, μ ω * (f ω - vbg_exp μ f) ^ 2 = 0 := by
    rw [← hvar]; unfold vbg_var; rw [vbg_cov_centered μ hμ]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have hnn : ∀ ω ∈ (Finset.univ : Finset Ω), 0 ≤ μ ω * (f ω - vbg_exp μ f) ^ 2 :=
    fun ω _ => mul_nonneg (hμ0 ω) (sq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  intro ω
  have := hzero ω (Finset.mem_univ ω)
  
  rcases mul_eq_zero.mp this with h | h
  · rw [h]; ring
  · have : f ω - vbg_exp μ f = 0 := by nlinarith [sq_nonneg (f ω - vbg_exp μ f)]
    rw [this]; ring


theorem vbg_thm1_degenerate (hμ0 : 0 ≤ μ) (hμ : ∑ ω, μ ω = 1) (hY : ∀ ω, Y ω * Y ω = Y ω)
    (hp0 : 0 < vbg_exp μ Y) (hp1 : vbg_exp μ Y < 1)
    (hVP : vbg_varPlus μ Y X = 0) (hVM : vbg_varMinus μ Y X = 0) :
    vbg_var μ Y * vbg_cov μ X Z = vbg_cov μ X Y * vbg_cov μ Y Z := by
  have hp0' := hp0
  have hYbnd : ∀ ω, Y ω ≤ 1 := by
    intro ω; nlinarith [hY ω, sq_nonneg (Y ω - 1), sq_nonneg (Y ω)]
  have hcompl0 : (0 : Ω → ℝ) ≤ (fun ω => 1 - Y ω) := by
    intro ω; show (0 : ℝ) ≤ 1 - Y ω; linarith [hYbnd ω]
  have hY0 : (0 : Ω → ℝ) ≤ Y := by
    intro ω; show (0:ℝ) ≤ Y ω; nlinarith [hY ω, sq_nonneg (Y ω)]
  set a₁ := vbg_exp (vbg_condPlus μ Y) X with ha1  
  set a₀ := vbg_exp (vbg_condMinus μ Y) X with ha0  
  
  have hpm := vbg_exp_one_sub (Y := Y) hμ
  have hq0 : 0 < vbg_exp μ (fun ω => 1 - Y ω) := by rw [hpm]; linarith
  have hplus := vbg_ae_const_of_var_zero (vbg_condPlus μ Y)
    (vbg_condPlus_nonneg hμ0 hY0 hp0) (vbg_condPlus_norm hp0) X hVP
  have hminus := vbg_ae_const_of_var_zero (vbg_condMinus μ Y)
    (by rw [vbg_condMinus_eq_condPlus hμ]; exact vbg_condPlus_nonneg hμ0 hcompl0 hq0)
    (by rw [vbg_condMinus_eq_condPlus hμ]; exact vbg_condPlus_norm hq0) X hVM
  
  have hplus' : ∀ ω, μ ω * Y ω * (X ω - a₁) = 0 := by
    intro ω
    have h := hplus ω
    
    have hp := congrArg (fun t => vbg_exp μ Y * t) h
    simp only [mul_zero] at hp
    rw [← ha1] at hp
    have hpe : vbg_exp μ Y * (vbg_condPlus μ Y ω * (X ω - a₁)) = μ ω * Y ω * (X ω - a₁) := by
      unfold vbg_condPlus; field_simp
    rw [hpe] at hp; exact hp
  have hminus' : ∀ ω, μ ω * (1 - Y ω) * (X ω - a₀) = 0 := by
    intro ω
    have h := hminus ω
    have hp := congrArg (fun t => vbg_exp μ (fun ω => 1 - Y ω) * t) h
    simp only [mul_zero] at hp
    rw [← ha0] at hp
    have hq_ne : (1 - vbg_exp μ Y) ≠ 0 := by intro h; apply absurd hp1; linarith [sub_eq_zero.mp h]
    have hpe : vbg_exp μ (fun ω => 1 - Y ω) * (vbg_condMinus μ Y ω * (X ω - a₀))
        = μ ω * (1 - Y ω) * (X ω - a₀) := by
      unfold vbg_condMinus; rw [hpm]; field_simp
    rw [hpe] at hp; exact hp
  
  have haffine : ∀ ω, μ ω * X ω = μ ω * (a₀ + (a₁ - a₀) * Y ω) := by
    intro ω
    have h1 := hplus' ω; have h2 := hminus' ω
    nlinarith [h1, h2, hY ω]
  
  set c := a₁ - a₀ with hc
  have eEX : vbg_exp μ X = a₀ + c * vbg_exp μ Y := by
    unfold vbg_exp
    rw [show (∑ ω, μ ω * X ω) = ∑ ω, μ ω * (a₀ + c * Y ω) from Finset.sum_congr rfl
      (fun ω _ => by rw [haffine ω])]
    rw [show (∑ ω, μ ω * (a₀ + c * Y ω)) = a₀ * (∑ ω, μ ω) + c * ∑ ω, μ ω * Y ω by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ω _ => by ring), hμ]
    ring
  have eEXZ : vbg_exp μ (fun ω => X ω * Z ω) = a₀ * vbg_exp μ Z + c * vbg_exp μ (fun ω => Y ω * Z ω) := by
    unfold vbg_exp
    rw [show (∑ ω, μ ω * (X ω * Z ω)) = ∑ ω, μ ω * ((a₀ + c * Y ω) * Z ω) from Finset.sum_congr rfl
      (fun ω _ => by rw [show μ ω * (X ω * Z ω) = (μ ω * X ω) * Z ω by ring, haffine ω]; ring)]
    rw [show (∑ ω, μ ω * ((a₀ + c * Y ω) * Z ω))
        = a₀ * (∑ ω, μ ω * Z ω) + c * ∑ ω, μ ω * (Y ω * Z ω) by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ω _ => by ring)]
  have eEXY : vbg_exp μ (fun ω => X ω * Y ω) = a₀ * vbg_exp μ Y + c * vbg_exp μ (fun ω => Y ω * Y ω) := by
    unfold vbg_exp
    rw [show (∑ ω, μ ω * (X ω * Y ω)) = ∑ ω, μ ω * ((a₀ + c * Y ω) * Y ω) from Finset.sum_congr rfl
      (fun ω _ => by rw [show μ ω * (X ω * Y ω) = (μ ω * X ω) * Y ω by ring, haffine ω]; ring)]
    rw [show (∑ ω, μ ω * ((a₀ + c * Y ω) * Y ω))
        = a₀ * (∑ ω, μ ω * Y ω) + c * ∑ ω, μ ω * (Y ω * Y ω) by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ω _ => by ring)]
  
  unfold vbg_var vbg_cov
  rw [eEX, eEXZ, eEXY]
  ring

end Degenerate


section Thm1

variable (μ : Ω → ℝ) (X Y Z : Ω → ℝ)


theorem vbg_thm1 (hμ0 : 0 ≤ μ) (hμ : ∑ ω, μ ω = 1) (hY : ∀ ω, Y ω * Y ω = Y ω)
    (hp0 : 0 < vbg_exp μ Y) (hp1 : vbg_exp μ Y < 1)
    (hCovP : 0 ≤ vbg_covPlus μ Y X Z) (hCovM : 0 ≤ vbg_covMinus μ Y X Z)
    (hnondeg : 0 < vbg_exp μ Y * vbg_varPlus μ Y X + (1 - vbg_exp μ Y) * vbg_varMinus μ Y X) :
    vbg_cov μ X Y * vbg_cov μ Y Z ≤ vbg_var μ Y * vbg_cov μ X Z := by
  set p := vbg_exp μ Y with hp
  
  have hid := vbg_prop1 μ X Y Z hY hp0 hp1
  rw [← hp] at hid
  
  have hRHS1 : 0 ≤ p * vbg_covPlus μ Y X Z + (1 - p) * vbg_covMinus μ Y X Z := by
    apply add_nonneg
    · exact mul_nonneg hp0.le hCovP
    · exact mul_nonneg (by linarith) hCovM
  have hRHS2 : 0 ≤ vbg_var μ X * vbg_var μ Y - vbg_cov μ X Y ^ 2 := by
    have hcs := vbg_cauchy_schwarz μ hμ0 hμ X Y
    
    nlinarith [hcs, vbg_var_nonneg μ hμ0 hμ X, vbg_var_nonneg μ hμ0 hμ Y]
  
  have hprodnn : 0 ≤ (vbg_var μ Y * vbg_cov μ X Z - vbg_cov μ X Y * vbg_cov μ Y Z)
      * (p * vbg_varPlus μ Y X + (1 - p) * vbg_varMinus μ Y X) := by
    rw [hid]; exact mul_nonneg hRHS1 hRHS2
  have hLHS1 : 0 ≤ vbg_var μ Y * vbg_cov μ X Z - vbg_cov μ X Y * vbg_cov μ Y Z :=
    nonneg_of_mul_nonneg_left hprodnn hnondeg
  linarith

end Thm1
end Prop1
end VBG
end Walls
end StatMech
