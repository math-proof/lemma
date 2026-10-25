/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptMConditional.Part6
import Def.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma truncInd_nonneg (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (t : ℕ) : 0 ≤ truncInd μ σ f U t := by
  unfold truncInd; split <;> norm_num


lemma adsD_fubini_lhs (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (t : ℕ) :
    (∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
          * truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n)))
      = ∫ U, fiberStep μ σ f t U * truncInd μ σ f U (t+1) ∂(Vcube n) := by
  have hint := integrable_abs_adapt_step_trunc μ σ hfC t
  rw [integral_prod _ hint]
  apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U
  simp only
  rw [integral_mul_const]; rfl


lemma adsD_integrable_fiberStep (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (t : ℕ) :
    Integrable (fun U => fiberStep μ σ f t U * truncInd μ σ f U (t+1)) (Vcube n) := by
  have hint := (integrable_abs_adapt_step_trunc μ σ hfC t).integral_prod_left
  simp only at hint
  refine hint.congr (Filter.Eventually.of_forall (fun U => ?_))
  show (∫ V, _ * _ ∂(Vcube n)) = fiberStep μ σ f t U * truncInd μ σ f U (t+1)
  rw [integral_mul_const]; rfl


lemma adsD_integrable_fiberDiag (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (e : E) (s : ℕ) (t : ℕ) :
    Integrable (fun U => fiberDiag μ σ f e s U * truncInd μ σ f U (t+1)) (Vcube n) := by
  have hint : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s))
        * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s)))
        * truncInd μ σ f p.1 (t+1)) ((Vcube n).prod (Vcube n)) := by
    refine ContinuousFKG.integrable_of_bdd _
      (((measurable_g_adaptWt μ σ f f s).mul (measurable_g_adaptWt μ σ f (Lindeberg.coord e) s)).mul
        ((measurable_truncInd μ σ f (t+1)).comp measurable_fst)) (C := (1*1)*1) (fun p => ?_)
    rw [abs_mul, abs_mul]
    refine mul_le_mul (mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _) (abs_nonneg _) (by norm_num))
      (truncInd_le_one μ σ f p.1 (t+1)) (abs_nonneg _) (by positivity)
  have hm := hint.integral_prod_left
  simp only at hm
  refine hm.congr (Filter.Eventually.of_forall (fun U => ?_))
  show (∫ V, _ * _ ∂(Vcube n)) = fiberDiag μ σ f e s U * truncInd μ σ f U (t+1)
  rw [integral_mul_const]; rfl


lemma adsD_integrable_fiberCross (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (e : E) (s₁ s₂ : ℕ) (t : ℕ) :
    Integrable (fun U => fiberCross μ σ f e s₁ s₂ U * truncInd μ σ f U (t+1)) (Vcube n) := by
  
  have hmf : Measurable (fun U : Fin n → ℝ =>
      ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₁)) ∂(Vcube n)) :=
    ((measurable_g_adaptWt μ σ f f s₁).stronglyMeasurable.integral_prod_right').measurable
  have hmg : Measurable (fun U : Fin n → ℝ =>
      ∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₂)) ∂(Vcube n)) :=
    ((measurable_g_adaptWt μ σ f (Lindeberg.coord e) s₂).stronglyMeasurable.integral_prod_right').measurable
  have hbf : ∀ U, |∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₁)) ∂(Vcube n)| ≤ 1 := by
    intro U
    calc |∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₁)) ∂(Vcube n)|
        ≤ ∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₁))| ∂(Vcube n) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ V, (1:ℝ) ∂(Vcube n) :=
          integral_mono (ContinuousFKG.integrable_of_bdd _
            (((measurable_g_adaptWt μ σ f f s₁).comp (measurable_const.prodMk measurable_id)).abs)
            (fun V => by rw [abs_abs]; exact hfC _))
            (integrable_const 1) (fun V => hfC _)
      _ = 1 := by simp
  have hbg : ∀ U, |∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₂)) ∂(Vcube n)| ≤ 1 := by
    intro U
    calc |∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₂)) ∂(Vcube n)|
        ≤ ∫ V, |Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₂))| ∂(Vcube n) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ V, (1:ℝ) ∂(Vcube n) :=
          integral_mono (ContinuousFKG.integrable_of_bdd _
            (((measurable_g_adaptWt μ σ f (Lindeberg.coord e) s₂).comp (measurable_const.prodMk measurable_id)).abs)
              (fun V => by rw [abs_abs]; exact GrandCoupling.abs_coord_le_one e _))
            (integrable_const 1) (fun V => GrandCoupling.abs_coord_le_one e _)
      _ = 1 := by simp
  refine ContinuousFKG.integrable_of_bdd _
    ((hmf.mul hmg).mul (measurable_truncInd μ σ f (t+1))) (C := (1*1)*1) (fun U => ?_)
  unfold fiberCross
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hbf U) (hbg U) (abs_nonneg _) (by norm_num))
    (truncInd_le_one μ σ f U (t+1)) (abs_nonneg _) (by positivity)


theorem adsD_adaptStepCovBound_of_condBBB {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) (hBBB : AdaptCondBBB μ σ f) :
    AdaptMConditional.AdaptStepCovBound μ σ f := by
  intro t htn
  set e := (σ : Fin n → E) ⟨t, htn⟩ with he
  
  rw [adsD_fubini_lhs μ σ hfC t]
  
  have hpt : ∀ U, fiberStep μ σ f t U * truncInd μ σ f U (t+1)
      ≤ (fiberDiag μ σ f e t U + fiberDiag μ σ f e (t+1) U
          - fiberCross μ σ f e t (t+1) U - fiberCross μ σ f e (t+1) t U)
        * truncInd μ σ f U (t+1) := by
    intro U
    unfold truncInd
    by_cases hev : t + 1 ≤ stopVal μ σ f U
    · rw [if_pos hev, mul_one, mul_one]
      
      
      have htn' : (t+1) - 1 < n := by simpa using htn
      have hbound := adsD_adapt_step_fiber_le hpos hmono σ hf hfC (t+1) (stopVal μ σ f U)
        (Nat.succ_le_succ (Nat.zero_le _)) hev htn' U
      
      
      unfold fiberStep fiberDiag fiberCross
      convert hbound using 2
    · rw [if_neg hev, mul_zero, mul_zero]
  
  refine (integral_mono (adsD_integrable_fiberStep μ σ hfC t) ?_ hpt).trans ?_
  · 
    have h1 := adsD_integrable_fiberDiag μ σ hfC e t t
    have h2 := adsD_integrable_fiberDiag μ σ hfC e (t+1) t
    have h3 := adsD_integrable_fiberCross μ σ hfC e t (t+1) t
    have h4 := adsD_integrable_fiberCross μ σ hfC e (t+1) t t
    have hcomb : (fun U => (fiberDiag μ σ f e t U + fiberDiag μ σ f e (t+1) U
          - fiberCross μ σ f e t (t+1) U - fiberCross μ σ f e (t+1) t U)
        * truncInd μ σ f U (t+1))
        = (fun U => fiberDiag μ σ f e t U * truncInd μ σ f U (t+1)
            + fiberDiag μ σ f e (t+1) U * truncInd μ σ f U (t+1)
            - fiberCross μ σ f e t (t+1) U * truncInd μ σ f U (t+1)
            - fiberCross μ σ f e (t+1) t U * truncInd μ σ f U (t+1)) := by
      funext U; ring
    rw [hcomb]
    exact ((h1.add h2).sub h3).sub h4
  · 
    obtain ⟨hD1, hD2, hC1, hC2⟩ := hBBB t htn
    set A1 := fun U => fiberDiag μ σ f e t U * truncInd μ σ f U (t+1) with hA1
    set A2 := fun U => fiberDiag μ σ f e (t+1) U * truncInd μ σ f U (t+1) with hA2
    set B1 := fun U => fiberCross μ σ f e t (t+1) U * truncInd μ σ f U (t+1) with hB1
    set B2 := fun U => fiberCross μ σ f e (t+1) t U * truncInd μ σ f U (t+1) with hB2
    have h1 : Integrable A1 (Vcube n) := adsD_integrable_fiberDiag μ σ hfC e t t
    have h2 : Integrable A2 (Vcube n) := adsD_integrable_fiberDiag μ σ hfC e (t+1) t
    have h3 : Integrable B1 (Vcube n) := adsD_integrable_fiberCross μ σ hfC e t (t+1) t
    have h4 : Integrable B2 (Vcube n) := adsD_integrable_fiberCross μ σ hfC e (t+1) t t
    have hsplit : (∫ U, (fiberDiag μ σ f e t U + fiberDiag μ σ f e (t+1) U
          - fiberCross μ σ f e t (t+1) U - fiberCross μ σ f e (t+1) t U)
        * truncInd μ σ f U (t+1) ∂(Vcube n))
      = (∫ U, A1 U ∂(Vcube n)) + (∫ U, A2 U ∂(Vcube n))
        - (∫ U, B1 U ∂(Vcube n)) - (∫ U, B2 U ∂(Vcube n)) := by
      rw [show (fun U => (fiberDiag μ σ f e t U + fiberDiag μ σ f e (t+1) U
            - fiberCross μ σ f e t (t+1) U - fiberCross μ σ f e (t+1) t U)
          * truncInd μ σ f U (t+1)) = (A1 + A2 - B1) - B2 from by
        funext U; simp only [Pi.add_apply, Pi.sub_apply, hA1, hA2, hB1, hB2]; ring]
      rw [integral_sub' ((h1.add h2).sub h3) h4]
      rw [show (∫ U, (A1 + A2 - B1) U ∂(Vcube n)) = ∫ U, ((A1 + A2) - B1) U ∂(Vcube n) from rfl]
      rw [integral_sub' (h1.add h2) h3, integral_add' h1 h2]
    rw [hsplit]
    
    set δ := ∫ U, truncInd μ σ f U (t+1) ∂(Vcube n) with hδ
    set Mfe := Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) with hMfe
    set Mf := Lindeberg.mean μ f with hMf
    set Mc := Lindeberg.mean μ (Lindeberg.coord e) with hMc
    
    have eA1 : (∫ U, A1 U ∂(Vcube n)) = Mfe * δ := hD1
    have eA2 : (∫ U, A2 U ∂(Vcube n)) = Mfe * δ := hD2
    have eB1 : Mf * Mc * δ ≤ ∫ U, B1 U ∂(Vcube n) := hC1
    have eB2 : Mf * Mc * δ ≤ ∫ U, B2 U ∂(Vcube n) := hC2
    have hcov : Lindeberg.cov μ f (Lindeberg.coord e) = Mfe - Mf * Mc := rfl
    have hδeq : δ = ∫ p, truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n)) := by
      rw [hδ, integral_prod _ (integrable_truncInd μ σ f (t+1))]
      apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U
      simp only; rw [integral_const]; simp
    rw [hcov, ← hδeq]
    
    rw [eA1, eA2]
    nlinarith [eB1, eB2]


theorem adsD_tree_osss_sharp {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hBBB : AdaptCondBBB μ σ f) :
    Lindeberg.var μ f
      ≤ ∑ e, AdaptMConditional.revealAdapt μ σ f e
          * Lindeberg.cov μ f (Lindeberg.coord e) := by
  have hf0' : ∀ ω, (0:ℝ) ≤ f ω := fun ω => hf0 ω
  have hfC : ∀ ω, |f ω| ≤ 1 := fun ω => by
    rw [abs_le]; exact ⟨by linarith [hf0' ω], hf1 ω⟩
  exact AdaptMConditional.tree_osss_sharp_unconditional hpos hμ1 σ hf0 hf1
    (adsD_adaptStepCovBound_of_condBBB hpos hmono σ hf hfC hBBB)

section FK

open StatMech.OSSS.MonotonicFK


theorem adsD_fk_q2_sharp {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {n : ℕ} (σ : Fin n ≃ Sym2 V) {f : ConfigSpace (Sym2 V) → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hBBB : AdaptCondBBB (fkMass G p 2) σ f) :
    Lindeberg.var (fkMass G p 2) f
      ≤ ∑ e, AdaptMConditional.revealAdapt (fkMass G p 2) σ f e
          * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
  adsD_tree_osss_sharp
    (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num))
    (fkMass_isMonotonic G hp hp1 (by norm_num)) σ hf hf0 hf1 hBBB

end FK
end AdaptDisintegration
end OSSS
end StatMech
