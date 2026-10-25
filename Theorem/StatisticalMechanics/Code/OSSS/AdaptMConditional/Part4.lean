/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptMConditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Def.StatisticalMechanics.Code.OSSS.AdaptMConditional.Part4
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


lemma truncInd_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (t : ℕ) : |truncInd μ σ f U t| ≤ 1 := by
  unfold truncInd; split <;> norm_num


lemma measurable_truncInd (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) :
    Measurable (fun U : Fin n → ℝ => truncInd μ σ f U t) := by
  unfold truncInd
  exact Measurable.ite (measurableSet_le measurable_const (measurable_stopVal μ σ f))
    measurable_const measurable_const


lemma abs_adapt_step_eq_mul_truncInd {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (U V : Fin n → ℝ) (t : ℕ) :
    |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t + 1)))
        - f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t))|
      = |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t + 1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t))|
        * truncInd μ σ f U (t + 1) := by
  unfold truncInd
  by_cases ht : t + 1 ≤ stopVal μ σ f U
  · rw [if_pos ht, mul_one]
  · 
    rw [if_neg ht, mul_zero]
    have hgt : stopVal μ σ f U < t + 1 := by omega
    have heq := adapt_step_eq_of_gt_stop σ U V (t + 1) hgt
    simp only [Nat.add_sub_cancel] at heq
    rw [heq, sub_self, abs_zero]


lemma integrable_abs_adapt_step (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (s₁ s₂ : ℕ) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₁))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₂))|)
      ((Vcube n).prod (Vcube n)) := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC (fun _ => false))
  refine StatMech.Probability.ContinuousFKG.integrable_of_bdd _
    (((measurable_g_adaptWt μ σ f f s₁).sub (measurable_g_adaptWt μ σ f f s₂)).abs)
    (C := 2*Cf) (fun p => ?_)
  rw [abs_abs]
  calc |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₁))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₂))|
      ≤ |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₁))|
        + |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₂))| := abs_sub _ _
    _ ≤ 2*Cf := by linarith [hfC (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₁)),
                              hfC (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₂))]


lemma integrable_abs_adapt_step_trunc (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (t : ℕ) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
        * truncInd μ σ f p.1 (t + 1))
      ((Vcube n).prod (Vcube n)) := by
  
  have hpt : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
        * truncInd μ σ f p.1 (t + 1))
      = (fun p => |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|) := by
    funext p; rw [← abs_adapt_step_eq_mul_truncInd σ p.1 p.2 t]
  rw [hpt]
  exact integrable_abs_adapt_step μ σ hfC (t+1) t


theorem trunc_telescope {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) :
    (∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) 0))
            - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n))|
            ∂((Vcube n).prod (Vcube n)))
      ≤ ∑ t ∈ Finset.range n,
          ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
                - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
                * truncInd μ σ f p.1 (t + 1)
            ∂((Vcube n).prod (Vcube n)) := by
  rw [← integral_finsetSum (Finset.range n)
    (fun t _ => integrable_abs_adapt_step_trunc μ σ hfC t)]
  apply integral_mono (integrable_abs_adapt_step μ σ hfC 0 n)
  · apply integrable_finsetSum; intro t _; exact integrable_abs_adapt_step_trunc μ σ hfC t
  · intro p
    set F : ℕ → ℝ := fun s => f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s)) with hF
    show |F 0 - F n| ≤ ∑ t ∈ Finset.range n,
        |F (t+1) - F t| * truncInd μ σ f p.1 (t + 1)
    
    have hcollapse : ∀ t, |F (t+1) - F t| * truncInd μ σ f p.1 (t + 1) = |F (t+1) - F t| := by
      intro t; rw [← abs_adapt_step_eq_mul_truncInd σ p.1 p.2 t]
    simp_rw [hcollapse]
    have htel : F 0 - F n = ∑ t ∈ Finset.range n, (F t - F (t+1)) := by
      rw [Finset.sum_range_sub' F n]
    rw [htel]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl; intro t _; rw [abs_sub_comm]


theorem var_le_trunc_telescope {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f
      ≤ (1/2) * ∑ t ∈ Finset.range n,
          ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
                - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
                * truncInd μ σ f p.1 (t + 1)
            ∂((Vcube n).prod (Vcube n)) := by
  have hf0' : ∀ ω, (0:ℝ) ≤ f ω := fun ω => hf0 ω
  have hfC : ∀ ω, |f ω| ≤ 1 := fun ω => by
    rw [abs_le]; exact ⟨by linarith [hf0' ω], hf1 ω⟩
  refine (var_le_adapt_first_step hpos hμ1 σ hf0 hf1).trans ?_
  exact mul_le_mul_of_nonneg_left (trunc_telescope σ hfC) (by norm_num : (0:ℝ) ≤ 1/2)


end AdaptMConditional
end OSSS
end StatMech
