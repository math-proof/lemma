/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLawClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailCondLaw.Part5
import Def.StatisticalMechanics.Code.OSSS.TailCondLawClose
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


lemma atl_jointMeas (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f g : ConfigSpace E → ℝ)
    (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (atl_selRand μ σ f t s A p))) := by
  have hjoin : Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      (acp_join t A p.1, p.2)) :=
    Measurable.prodMk
      ((ubfSplit n t).symm.measurable.comp (measurable_const.prodMk measurable_fst))
      measurable_snd
  exact (measurable_g_adaptWt μ σ f g s).comp hjoin


theorem atl_tailSelMP_of_stop_le {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (hstop : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) ≤ s) :
    atl_TailSelMP μ σ f t s A := by
  have heq : atl_selRand μ σ f t s A = Prod.snd := by
    funext p
    show adaptWt (acp_join t A p.1) p.2 (stopVal μ σ f (acp_join t A p.1)) s = p.2
    exact adaptWt_ge_stop _ _ _ s (hstop p.1)
  show MeasurePreserving (atl_selRand μ σ f t s A) ((ubfTail n t).prod (Vcube n)) (Vcube n)
  rw [heq]
  exact measurePreserving_snd


theorem atl_innerRand_eq_mean (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (g : ConfigSpace E → ℝ) {Cg : ℝ} (hgC : ∀ ω, |g ω| ≤ Cg) (t s : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) (hMP : atl_TailSelMP μ σ f t s A) :
    (∫ B, (∫ V, g (codeMap μ (σ : Fin n → E)
            (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s)) ∂(Vcube n))
        ∂(ubfTail n t))
      = Lindeberg.mean μ g := by
  have hint : Integrable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (atl_selRand μ σ f t s A p)))
      ((ubfTail n t).prod (Vcube n)) :=
    ContinuousFKG.integrable_of_bdd _ (atl_jointMeas μ σ f g t s A) (fun p => hgC _)
  
  have hfub : (∫ p, g (codeMap μ (σ : Fin n → E) (atl_selRand μ σ f t s A p))
        ∂((ubfTail n t).prod (Vcube n)))
      = ∫ B, (∫ V, g (codeMap μ (σ : Fin n → E)
            (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) s)) ∂(Vcube n))
          ∂(ubfTail n t) := by
    rw [integral_prod _ hint]; rfl
  
  have hmean : (∫ p, g (codeMap μ (σ : Fin n → E) (atl_selRand μ σ f t s A p))
        ∂((ubfTail n t).prod (Vcube n)))
      = ∑ x, g x * μ x := by
    have hcomp : (∫ p, (fun w => g (codeMap μ (σ : Fin n → E) w)) (atl_selRand μ σ f t s A p)
          ∂((ubfTail n t).prod (Vcube n)))
        = ∫ w, g (codeMap μ (σ : Fin n → E) w) ∂(Vcube n) := by
      rw [← hMP.map_eq, integral_map hMP.measurable.aemeasurable
        (measurable_g_codeMap μ σ g).aestronglyMeasurable, hMP.map_eq]
    rw [hcomp, integral_g_codeMap μ hpos hμ1 σ g]
  rw [← hfub, hmean]; rfl


theorem atl_diag_of_MP (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (e : E)
    (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (hMP : atl_TailSelMP μ σ f t s A) :
    (∫ B, fiberDiag μ σ f e s (acp_join t A B) ∂(ubfTail n t))
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) := by
  have hgC : ∀ ω, |f ω * Lindeberg.coord e ω| ≤ 1 := by
    intro ω; rw [abs_mul, ← one_mul (1 : ℝ)]
    exact mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _) (abs_nonneg _) (by norm_num)
  exact atl_innerRand_eq_mean μ hpos hμ1 σ (fun ω => f ω * Lindeberg.coord e ω) hgC t s A hMP


end AdaptDisintegration
end OSSS
end StatMech
