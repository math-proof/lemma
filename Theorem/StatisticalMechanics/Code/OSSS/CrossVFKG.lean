/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CrossVFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.MargMonoRand
import Theorem.StatisticalMechanics.Code.OSSS.SpliceST1.Part4
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


lemma cvf_coord_local (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (t : ℕ) (htn : t < n)
    (w w' : Fin n → ℝ) (h : ∀ i : Fin n, (i:ℕ) < t+1 → w i = w' i) :
    codeMap μ (σ : Fin n → E) w ((σ : Fin n → E) ⟨t, htn⟩)
      = codeMap μ (σ : Fin n → E) w' ((σ : Fin n → E) ⟨t, htn⟩) := by
  have hval : ∀ v : Fin n → ℝ,
      codeMap μ (σ : Fin n → E) v ((σ : Fin n → E) ⟨t, htn⟩)
        = codePrefix μ (σ : Fin n → E) v (t+1) ((σ : Fin n → E) ⟨t, htn⟩) := by
    intro v; unfold codeMap
    exact codePrefix_stable μ (σ : Fin n → E) σ.injective v (t+1) n htn ((σ : Fin n → E) ⟨t, htn⟩)
      (by rw [mem_prefixSet_iff]; exact ⟨⟨t, htn⟩, Nat.lt_succ_self t, rfl⟩)
  rw [hval w, hval w', codePrefix_congr_of_agree μ (σ : Fin n → E) w w' (t+1) htn h]


lemma cvf_coordMarg_const_succ (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B B' : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
    atl_margRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t (t+1) A B
      = atl_margRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t (t+1) A B' := by
  unfold atl_margRand
  congr 1
  funext V
  have hcoord : codeMap μ (σ : Fin n → E)
        (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) (t+1))
        ((σ : Fin n → E) ⟨t, htn⟩)
      = codeMap μ (σ : Fin n → E)
        (adaptWt (acp_join t A B') V (stopVal μ σ f (acp_join t A B')) (t+1))
        ((σ : Fin n → E) ⟨t, htn⟩) :=
    cvf_coord_local μ σ t htn _ _
      (fun i hi => by
        show adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) (t+1) i
          = adaptWt (acp_join t A B') V (stopVal μ σ f (acp_join t A B')) (t+1) i
        unfold adaptWt; simp only [hi, if_true])
  unfold Lindeberg.coord
  rw [hcoord]


theorem cvf_cross_succ_eq (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1)
    (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    (∫ B, fiberCross μ σ f ((σ : Fin n → E) ⟨t, htn⟩) t (t+1) (acp_join t A B) ∂(ubfTail n t))
      = Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) := by
  classical
  set e := (σ : Fin n → E) ⟨t, htn⟩ with he
  set M₁ := atl_margRand μ σ f f t t A with hM₁
  set M₂ := atl_margRand μ σ f (Lindeberg.coord e) t (t+1) A with hM₂
  set B₀ : {i : Fin n // ¬ (i : ℕ) < t} → ℝ := fun _ => 0 with hB₀
  set c := M₂ B₀ with hc
  
  have hcross : (∫ B, fiberCross μ σ f e t (t+1) (acp_join t A B) ∂(ubfTail n t))
      = ∫ B, M₁ B * c ∂(ubfTail n t) := by
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro B
    show atl_margRand μ σ f f t t A B * atl_margRand μ σ f (Lindeberg.coord e) t (t+1) A B
      = M₁ B * c
    rw [hc]; congr 1
    exact cvf_coordMarg_const_succ μ σ f t htn A B B₀
  
  have hpull : (∫ B, M₁ B * c ∂(ubfTail n t)) = (∫ B, M₁ B ∂(ubfTail n t)) * c :=
    integral_mul_const _ _
  
  have hM₁mean : (∫ B, M₁ B ∂(ubfTail n t)) = Lindeberg.mean μ f :=
    atl_marg_of_MP μ hpos hμ1 σ f hfC t t A (tsc_tailSelMP_at_s_eq_t μ σ f t A)
  
  have hM₂const : (∫ B, M₂ B ∂(ubfTail n t)) = c := by
    rw [show (fun B => M₂ B) = (fun _ => c) from funext (fun B => by
      rw [hc]; exact cvf_coordMarg_const_succ μ σ f t htn A B B₀)]
    rw [integral_const, show (ubfTail n t).real Set.univ = 1 from probReal_univ, one_smul]
  have hM₂mean : (∫ B, M₂ B ∂(ubfTail n t)) = Lindeberg.mean μ (Lindeberg.coord e) :=
    atl_marg_of_MP μ hpos hμ1 σ (Lindeberg.coord e)
      (fun ω => GrandCoupling.abs_coord_le_one e ω) t (t+1) A (sp1_tailSelMP μ σ f t htn A)
  have hcμ : c = Lindeberg.mean μ (Lindeberg.coord e) := by rw [← hM₂const, hM₂mean]
  rw [hcross, hpull, hM₁mean, hcμ]


theorem cvf_cross_succ (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1)
    (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩))
      ≤ ∫ B, fiberCross μ σ f ((σ : Fin n → E) ⟨t, htn⟩) t (t+1) (acp_join t A B) ∂(ubfTail n t) :=
  le_of_eq (cvf_cross_succ_eq μ hpos hμ1 σ hfC t htn A).symm


end AdaptDisintegration
end OSSS
end StatMech
