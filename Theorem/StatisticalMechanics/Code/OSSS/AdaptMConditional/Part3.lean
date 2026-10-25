/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Def.StatisticalMechanics.Code.OSSS.AdaptMConditional.Part3
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptMConditional

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.LindebergTree OSSS.AdaptiveTau

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma stopVal_eq_stopValC (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) :
    stopVal μ σ f U = stopValC σ f (codeMap μ (σ : Fin n → E) U) := rfl


lemma stopVal_le (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (U : Fin n → ℝ) : stopVal μ σ f U ≤ n :=
  Nat.find_le (detAtC_card σ f (codeMap μ (σ : Fin n → E) U))


lemma stopVal_determines (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) :
    detAtC (σ : Fin n → E) f (codeMap μ (σ : Fin n → E) U) (stopVal μ σ f U) :=
  Nat.find_spec (⟨n, detAtC_card σ f (codeMap μ (σ : Fin n → E) U)⟩ :
    ∃ t, detAtC (σ : Fin n → E) f (codeMap μ (σ : Fin n → E) U) t)


lemma codeMap_agree_on_prefix (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (w w' : Fin n → ℝ) (k : ℕ)
    (hagree : ∀ i : Fin n, (i : ℕ) < k → w i = w' i) :
    ∀ e ∈ prefixSet (σ : Fin n → E) k,
      codeMap μ (σ : Fin n → E) w e = codeMap μ (σ : Fin n → E) w' e := by
  intro e he
  rw [mem_prefixSet_iff] at he
  obtain ⟨i, hik, rfl⟩ := he
  
  have hstab : ∀ v : Fin n → ℝ,
      codeMap μ (σ : Fin n → E) v ((σ : Fin n → E) i)
        = codePrefix μ (σ : Fin n → E) v (i + 1) ((σ : Fin n → E) i) := by
    intro v
    unfold codeMap
    exact codePrefix_stable μ (σ : Fin n → E) σ.injective v (i + 1) n i.2
      ((σ : Fin n → E) i)
      (by rw [mem_prefixSet_iff]; exact ⟨i, Nat.lt_succ_self _, rfl⟩)
  rw [hstab w, hstab w']
  
  have hi1k : i + 1 ≤ k := by omega
  rw [codePrefix_congr_of_agree μ (σ : Fin n → E) w w' (i + 1) (by omega)
    (fun j hj => hagree j (by omega))]


theorem f_adapt_zero_eq {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (U V : Fin n → ℝ) :
    f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) 0))
      = f (codeMap μ (σ : Fin n → E) U) := by
  set m := stopVal μ σ f U with hm
  rw [adaptWt_zero]
  
  have hagree : ∀ i : Fin n, (i : ℕ) < m → (mixUV U V m) i = U i := by
    intro i hi; unfold mixUV; simp [hi]
  
  have hpref : ∀ e ∈ prefixSet (σ : Fin n → E) m,
      codeMap μ (σ : Fin n → E) (mixUV U V m) e = codeMap μ (σ : Fin n → E) U e :=
    codeMap_agree_on_prefix μ σ (mixUV U V m) U m hagree
  
  exact stopVal_determines μ σ f U (codeMap μ (σ : Fin n → E) (mixUV U V m)) hpref


theorem adapt_step_eq_of_gt_stop {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (U V : Fin n → ℝ) (t : ℕ) (ht : stopVal μ σ f U < t) :
    codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t)
      = codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t - 1)) := by
  set m := stopVal μ σ f U with hm
  rw [adaptWt_ge_stop U V m t (by omega), adaptWt_ge_stop U V m (t - 1) (by omega)]


lemma measurable_stopVal (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) :
    Measurable (fun U : Fin n → ℝ => stopVal μ σ f U) := by
  have : (fun U : Fin n → ℝ => stopVal μ σ f U)
      = (fun X => stopValC σ f X) ∘ (fun U => codeMap μ (σ : Fin n → E) U) := rfl
  rw [this]
  exact (measurable_of_countable _).comp (measurable_codeMap μ σ)


lemma measurable_mixUV {n : ℕ} (m : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => mixUV p.1 p.2 m) := by
  apply measurable_pi_lambda
  intro i; unfold mixUV
  by_cases h : (i : ℕ) < m
  · simp only [h, if_true]; exact (measurable_pi_apply i).comp measurable_fst
  · simp only [h, if_false]; exact (measurable_pi_apply i).comp measurable_snd


lemma measurable_adaptWt_fixed {n : ℕ} (m s : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => adaptWt p.1 p.2 m s) := by
  have hrw : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => adaptWt p.1 p.2 m s)
      = (fun p => Wt (mixUV p.1 p.2 m) p.2 s) := by
    funext p; rw [adaptWt_eq_Wt_mix]
  rw [hrw]
  apply measurable_pi_lambda
  intro i; unfold Wt
  by_cases h : (i : ℕ) < s
  · simp only [h, if_true]; exact (measurable_pi_apply i).comp measurable_snd
  · simp only [h, if_false]
    exact (measurable_pi_apply i).comp (measurable_mixUV m)


lemma measurable_g_adaptWt (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) (s : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s))) := by
  
  have hstop : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => stopVal μ σ f p.1) :=
    (measurable_stopVal μ σ f).comp measurable_fst
  
  
  have key : ∀ m : ℕ, Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) :=
    fun m => (measurable_g_codeMap μ σ g).comp (measurable_adaptWt_fixed m s)
  
  have hglue : Measurable (fun mp : ℕ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      g (codeMap μ (σ : Fin n → E) (adaptWt mp.2.1 mp.2.2 mp.1 s))) :=
    measurable_from_prod_countable_right key
  exact hglue.comp (hstop.prodMk measurable_id)


theorem var_le_adapt_first_step {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f
      ≤ (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) 0))
            - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n))|
            ∂((Vcube n).prod (Vcube n)) := by
  
  have hpt : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) 0))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n))|)
      = (fun p => |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0))
          - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n))|) := by
    funext p
    rw [f_adapt_zero_eq (μ := μ) (f := f) σ p.1 p.2, adaptWt_card, Wt_zero, Wt_card]
  rw [hpt]
  exact var_le_grandCoupling_first_step hpos hμ1 σ hf0 hf1


end AdaptMConditional
end OSSS
end StatMech
