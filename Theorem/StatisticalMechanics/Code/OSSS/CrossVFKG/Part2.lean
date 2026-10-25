/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossVFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.MargMonoRand
import Theorem.StatisticalMechanics.Code.OSSS.SpliceST1.Part4
import Def.StatisticalMechanics.Code.OSSS.CrossVFKG
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


theorem cvf_Cross41_of_margMono (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1)
    (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (hmono1 : atl_MargMonoRand μ σ f f t (t+1) A)
    (hmono2 : atl_MargMonoRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t t A) :
    cvf_Cross41 μ σ f t htn A :=
  atl_cross_of_MP_mono μ hpos hμ1 σ hfC ((σ : Fin n → E) ⟨t, htn⟩) t (t+1) t A
    (sp1_tailSelMP μ σ f t htn A) (tsc_tailSelMP_at_s_eq_t μ σ f t A) hmono1 hmono2


theorem cvf_Cross41_const_switch {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1)
    (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (m₀ : ℕ)
    (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = m₀) :
    cvf_Cross41 μ σ f t htn A :=
  cvf_Cross41_of_margMono μ hpos hμ1 σ hfC t htn A
    (atl_margMonoRand_of_const hpos hmono σ hf hfC t (t+1) A m₀ hconst)
    (atl_margMonoRand_of_const hpos hmono σ (Lindeberg.coord_mono _)
      (fun ω => GrandCoupling.abs_coord_le_one _ ω) t t A m₀ hconst)


theorem cvf_tailCondLaw_of_cross41 {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1)
    (hCross41 : ∀ (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ),
        cvf_Cross41 μ σ f t htn A) :
    acp_TailCondLaw μ σ f := by
  intro t htn A
  set e := (σ : Fin n → E) ⟨t, htn⟩ with he
  refine ⟨?_, ?_, ?_, ?_⟩
  · 
    exact atl_diag_of_MP μ hpos hμ1 σ hfC e t t A (tsc_tailSelMP_at_s_eq_t μ σ f t A)
  · 
    exact atl_diag_of_MP μ hpos hμ1 σ hfC e t (t+1) A (sp1_tailSelMP μ σ f t htn A)
  · 
    exact cvf_cross_succ μ hpos hμ1 σ hfC t htn A
  · 
    exact hCross41 t htn A


theorem cvf_tailCondLaw_const_switch {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1)
    (cvf_const : ∀ (t : ℕ), ({i : Fin n // (i : ℕ) < t} → ℝ) → ℕ)
    (hconst : ∀ (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
        (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ),
        stopVal μ σ f (acp_join t A B) = cvf_const t A) :
    acp_TailCondLaw μ σ f :=
  cvf_tailCondLaw_of_cross41 hpos hμ1 σ hfC
    (fun t htn A => cvf_Cross41_const_switch hpos hμ1 hmono σ hf hfC t htn A (cvf_const t A)
      (fun B => hconst t A B))

end AdaptDisintegration
end OSSS
end StatMech
