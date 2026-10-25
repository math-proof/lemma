/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptMConditional.Part6
import Def.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part3
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


lemma adsD_selMap2_eq_adaptWt (n s m : ℕ) (U V : Fin n → ℝ) :
    selMap2 n s m (U, V) = adaptWt U V m s := by
  funext i
  unfold selMap2 projInl adaptWt
  rw [MeasurableEquiv.coe_piCongrLeft]
  simp only [Equiv.piCongrLeft_apply, eq_rec_constant]
  rw [sw2Equiv_symm_apply, combine_apply]
  simp only [sw2]
  by_cases h : (i : ℕ) < s
  · rw [if_pos (Or.inl h)]; simp [h]
  · by_cases h2 : (i : ℕ) < m
    · have hcond : ¬ ((i:ℕ) < s ∨ (i:ℕ) ≥ m) := by
        rintro (hc | hc) <;> omega
      rw [if_neg hcond]; simp [h, h2]
    · have hcond : (i:ℕ) < s ∨ (i:ℕ) ≥ m := Or.inr (by omega)
      rw [if_pos hcond]; simp [h, h2]


lemma adsD_selMap2_measurePreserving (n s m : ℕ) :
    MeasurePreserving (selMap2 n s m) ((Vcube n).prod (Vcube n)) (Vcube n) := by
  show MeasurePreserving (selMap2 n s m)
    ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
    (Measure.pi (fun _ : Fin n => unitMeasure))
  have hcombine : MeasurePreserving (combine n)
      ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure)) :=
    (measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin n => ℝ)
      (fun _ : Fin n ⊕ Fin n => unitMeasure)).symm _
  have hperm : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => ℝ) (sw2Equiv n s m))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure)) := by
    have h := measurePreserving_piCongrLeft (fun _ : Fin n ⊕ Fin n => unitMeasure) (sw2Equiv n s m)
    convert h using 2
  have hproj : MeasurePreserving (projInl n)
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure))
      (Measure.pi (fun _ : Fin n => unitMeasure)) := by
    have hsum := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin n => ℝ)
      (fun _ : Fin n ⊕ Fin n => unitMeasure)
    have hfst : MeasurePreserving Prod.fst
        ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
        (Measure.pi (fun _ : Fin n => unitMeasure)) := measurePreserving_fst
    have := hfst.comp hsum
    convert this using 1
  have := (hproj.comp hperm).comp hcombine
  convert this using 1


theorem adsD_integral_g_adaptWt_fixed (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) (s m : ℕ) :
    ∫ p, g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s)) ∂((Vcube n).prod (Vcube n))
      = ∑ x, g x * μ x := by
  have hmp := adsD_selMap2_measurePreserving n s m
  have hcomp : ∫ p, (fun w => g (codeMap μ (σ : Fin n → E) w)) (selMap2 n s m p)
        ∂((Vcube n).prod (Vcube n))
      = ∫ w, g (codeMap μ (σ : Fin n → E) w) ∂(Vcube n) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
      (measurable_g_codeMap μ σ g).aestronglyMeasurable, hmp.map_eq]
  have hrw : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (fun w => g (codeMap μ (σ : Fin n → E) w)) (selMap2 n s m p))
      = (fun p => g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) := by
    funext p; rw [show p = (p.1, p.2) from rfl, adsD_selMap2_eq_adaptWt]
  rw [hrw] at hcomp
  rw [hcomp, integral_g_codeMap μ hpos hμ1 σ g]


lemma adsD_measurable_f_adaptWt_fiber (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (m s : ℕ) :
    Measurable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (adaptWt U V m s))) := by
  have hrw : (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (adaptWt U V m s)))
      = (fun V => f (codeMap μ (σ : Fin n → E) (Wt (mixUV U V m) V s))) := by
    funext V; rw [adaptWt_eq_Wt_mix]
  rw [hrw]
  refine (measurable_g_codeMap μ σ f).comp ?_
  apply measurable_pi_lambda
  intro i; unfold Wt mixUV
  by_cases h : (i : ℕ) < s
  · simp only [h, if_true]; exact measurable_pi_apply i
  · simp only [h, if_false]
    by_cases h2 : (i : ℕ) < m
    · simp only [h2, if_true]; exact measurable_const
    · simp only [h2, if_false]; exact measurable_pi_apply i


lemma adsD_measurable_f_adaptWt_prod (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) (m s : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) :=
  (measurable_g_codeMap μ σ g).comp (measurable_adaptWt_fixed m s)


lemma adsD_adaptWt_mono_V {n : ℕ} (U : Fin n → ℝ) (m s : ℕ) :
    Monotone (fun V : Fin n → ℝ => adaptWt U V m s) := by
  intro V V' hle i
  unfold adaptWt
  by_cases h : (i : ℕ) < s
  · simp only [h, if_true]; exact hle i
  · simp only [h, if_false]
    by_cases h2 : (i : ℕ) < m
    · simp only [h2, if_true]; exact le_refl _
    · simp only [h2, if_false]; exact hle i


lemma adsD_f_adaptWt_mono_V {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (U : Fin n → ℝ) (m s : ℕ) :
    Monotone (fun V : Fin n → ℝ => f (codeMap μ σ (adaptWt U V m s))) :=
  fun _ _ hle => hf ((codeMap_mono_u hpos hmono σ) ((adsD_adaptWt_mono_V U m s) hle))


lemma adsD_coord_adaptWt_mono_V {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) (e : E) (U : Fin n → ℝ) (m s : ℕ) :
    Monotone (fun V : Fin n → ℝ => Lindeberg.coord e (codeMap μ σ (adaptWt U V m s))) :=
  fun _ _ hle =>
    Lindeberg.coord_mono e ((codeMap_mono_u hpos hmono σ) ((adsD_adaptWt_mono_V U m s) hle))


lemma adsD_integrable_prod_obs_fiber (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (U : Fin n → ℝ)
    (m s₁ s₂ : ℕ) :
    Integrable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁))
        * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂))) (Vcube n) := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC (fun _ => false))
  refine ContinuousFKG.integrable_of_bdd _
    ((adsD_measurable_f_adaptWt_fiber μ σ f U m s₁).mul
      (adsD_measurable_f_adaptWt_fiber μ σ (Lindeberg.coord e) U m s₂))
    (C := Cf * 1) (fun V => ?_)
  rw [abs_mul]
  exact mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _) (abs_nonneg _) hCf0


theorem adsD_abs_adapt_step_eq_four_terms {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (t m : ℕ) (ht : 1 ≤ t) (htm : t ≤ m) (htn : t - 1 < n)
    (U V : Fin n → ℝ) :
    |f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
        - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))|
      = f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
        + f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
        - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
        - f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) := by
  set k := t - 1 with hk
  set e := (σ : Fin n → E) ⟨k, htn⟩ with he
  set Yt := codeMap μ (σ : Fin n → E) (adaptWt U V m t) with hYt
  set Ys := codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)) with hYs
  
  have hoff : ∀ i : Fin n, (i:ℕ) ≠ k → adaptWt U V m t i = adaptWt U V m (t-1) i :=
    adaptWt_agree_off U V m t ht
  
  have hdet : Lindeberg.coord e Yt = Lindeberg.coord e Ys → Yt = Ys := by
    intro hcoord
    have hbit : Yt e = Ys e := by
      unfold Lindeberg.coord at hcoord
      by_cases h1 : Yt e <;> by_cases h2 : Ys e <;> simp_all
    exact codeMap_det μ (σ : Fin n → E) σ.injective (adaptWt U V m t) (adaptWt U V m (t-1)) k htn
      (fun i hi => hoff i hi) hbit
  
  obtain ⟨hVt, hUt⟩ := adaptWt_at_pos U V m t ht htm htn
  
  have hcmp : (f Ys ≤ f Yt ∧ Lindeberg.coord e Ys ≤ Lindeberg.coord e Yt)
      ∨ (f Yt ≤ f Ys ∧ Lindeberg.coord e Yt ≤ Lindeberg.coord e Ys) := by
    rcases le_total (U ⟨k, htn⟩) (V ⟨k, htn⟩) with hUV | hVU
    · left
      have hle : adaptWt U V m (t-1) ≤ adaptWt U V m t := by
        intro i
        by_cases hi : (i:ℕ) = k
        · have hieq : i = ⟨k, htn⟩ := by ext; rw [hi]
          rw [hieq, hVt, hUt]; exact hUV
        · rw [hoff i hi]
      have hY : Ys ≤ Yt := codeMap_mono_u hpos hmono (σ : Fin n → E) hle
      exact ⟨hf hY, Lindeberg.coord_mono e hY⟩
    · right
      have hle : adaptWt U V m t ≤ adaptWt U V m (t-1) := by
        intro i
        by_cases hi : (i:ℕ) = k
        · have hieq : i = ⟨k, htn⟩ := by ext; rw [hi]
          rw [hieq, hVt, hUt]; exact hVU
        · rw [hoff i hi]
      have hY : Yt ≤ Ys := codeMap_mono_u hpos hmono (σ : Fin n → E) hle
      exact ⟨hf hY, Lindeberg.coord_mono e hY⟩
  exact tt_algebra (f Yt) (f Ys) (Lindeberg.coord e Yt) (Lindeberg.coord e Ys)
    (coord_eq01 e Yt) (coord_eq01 e Ys) hcmp (fun h => by rw [hdet h])


theorem adsD_abs_adapt_step_integral_fiber {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf)
    (t m : ℕ) (ht : 1 ≤ t) (htm : t ≤ m) (htn : t - 1 < n) (U : Fin n → ℝ) :
    (∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
            - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))| ∂(Vcube n))
      = (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n))
        + (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n)) := by
  set e := (σ : Fin n → E) ⟨t-1, htn⟩ with he
  set D1 := fun V => f (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1)))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1))) with hD1
  set D2 := fun V => f (codeMap μ (σ:Fin n→E) (adaptWt U V m t))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m t)) with hD2
  set C1 := fun V => f (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1)))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m t)) with hC1
  set C2 := fun V => f (codeMap μ (σ:Fin n→E) (adaptWt U V m t))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1))) with hC2
  have hI1 : Integrable D1 (Vcube n) := adsD_integrable_prod_obs_fiber μ σ hfC e U m (t-1) (t-1)
  have hI2 : Integrable D2 (Vcube n) := adsD_integrable_prod_obs_fiber μ σ hfC e U m t t
  have hIc1 : Integrable C1 (Vcube n) := adsD_integrable_prod_obs_fiber μ σ hfC e U m (t-1) t
  have hIc2 : Integrable C2 (Vcube n) := adsD_integrable_prod_obs_fiber μ σ hfC e U m t (t-1)
  have hcongr : (∫ V, |f (codeMap μ (σ:Fin n→E) (adaptWt U V m t))
            - f (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1)))| ∂(Vcube n))
      = ∫ V, (D1 V + D2 V - C1 V - C2 V) ∂(Vcube n) := by
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro V
    exact adsD_abs_adapt_step_eq_four_terms hpos hmono σ hf t m ht htm htn U V
  rw [hcongr]
  have esplit : (fun V => D1 V + D2 V - C1 V - C2 V) = (D1 + D2 - C1) - C2 := by
    funext V; simp only [Pi.add_apply, Pi.sub_apply]
  rw [show (∫ V, (D1 V + D2 V - C1 V - C2 V) ∂(Vcube n))
        = ∫ V, ((D1 + D2 - C1) - C2) V ∂(Vcube n) from by rw [esplit]]
  rw [integral_sub' ((hI1.add hI2).sub hIc1) hIc2]
  rw [show (∫ V, (D1 + D2 - C1) V ∂(Vcube n)) = ∫ V, ((D1 + D2) - C1) V ∂(Vcube n) from rfl]
  rw [integral_sub' (hI1.add hI2) hIc1, integral_add' hI1 hI2]


theorem adsD_adapt_fkg_cross_fiber {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (m s₁ s₂ : ℕ)
    (U : Fin n → ℝ) :
    (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁)) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂)) ∂(Vcube n) := by
  refine fkg_second_block_fiber
    (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s₁)))
    (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s₂)))
    (adsD_measurable_f_adaptWt_prod μ σ f m s₁)
    (adsD_measurable_f_adaptWt_prod μ σ (Lindeberg.coord e) m s₂)
    (Cf := Cf) (Cg := 1) (fun z => hfC _) (fun z => GrandCoupling.abs_coord_le_one e _)
    ?_ ?_ U
  · intro Ufix V V' hVV
    exact hf ((codeMap_mono_u hpos hmono (σ : Fin n → E)) ((adsD_adaptWt_mono_V Ufix m s₁) hVV))
  · intro Ufix V V' hVV
    exact Lindeberg.coord_mono e
      ((codeMap_mono_u hpos hmono (σ : Fin n → E)) ((adsD_adaptWt_mono_V Ufix m s₂) hVV))


theorem adsD_adapt_step_fiber_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf)
    (t m : ℕ) (ht : 1 ≤ t) (htm : t ≤ m) (htn : t - 1 < n) (U : Fin n → ℝ) :
    (∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
            - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))| ∂(Vcube n))
      ≤ (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n))
        + (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n))
            * (∫ V, Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n))
            * (∫ V, Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n)) := by
  set e := (σ : Fin n → E) ⟨t-1, htn⟩ with he
  rw [adsD_abs_adapt_step_integral_fiber hpos hmono σ hf hfC t m ht htm htn U]
  have key1 : (∫ V, f (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1))) ∂(Vcube n))
      * (∫ V, Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m t)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1)))
            * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m t)) ∂(Vcube n) :=
    adsD_adapt_fkg_cross_fiber hpos hmono σ hf hfC e m (t-1) t U
  have key2 : (∫ V, f (codeMap μ (σ:Fin n→E) (adaptWt U V m t)) ∂(Vcube n))
      * (∫ V, Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1))) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ:Fin n→E) (adaptWt U V m t))
            * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1))) ∂(Vcube n) :=
    adsD_adapt_fkg_cross_fiber hpos hmono σ hf hfC e m t (t-1) U
  linarith [key1, key2]


end AdaptDisintegration
end OSSS
end StatMech
