/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptCondReduction
import Def.StatisticalMechanics.Code.OSSS.TailCondLaw.Part3
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


theorem atc_tailCondLawFixedCross {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) (e : E)
    (t s₁ s₂ m : ℕ) (hst1 : t ≤ s₁) (hst2 : t ≤ s₂)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
      ≤ ∫ B, atc_fiberCrossFixed μ σ f e m s₁ s₂ (acp_join t A B) ∂(ubfTail n t) := by
  set φ₁ : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) → ℝ := fun B =>
    ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s₁)) ∂(Vcube n) with hφ₁
  set φ₂ : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) → ℝ := fun B =>
    ∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s₂)) ∂(Vcube n)
    with hφ₂
  
  have hcross : (∫ B, atc_fiberCrossFixed μ σ f e m s₁ s₂ (acp_join t A B) ∂(ubfTail n t))
      = ∫ B, φ₁ B * φ₂ B ∂(ubfTail n t) := rfl
  rw [hcross]
  
  have hFKG := atc_hasFKG_ubfTail n t φ₁ φ₂
    (atc_marg_meas_B μ σ f t m s₁ A) (atc_marg_meas_B μ σ (Lindeberg.coord e) t m s₂ A)
    ⟨1, fun B => atc_marg_le_one μ σ hfC t m s₁ A B⟩
    ⟨1, fun B => atc_marg_le_one μ σ (fun ω => GrandCoupling.abs_coord_le_one e ω) t m s₂ A B⟩
    (atc_marg_mono_B hpos hmono σ hf hfC t m s₁ A)
    (atc_marg_mono_B hpos hmono σ (Lindeberg.coord_mono e)
      (fun ω => GrandCoupling.abs_coord_le_one e ω) t m s₂ A)
  
  have hm1 : (∫ B, φ₁ B ∂(ubfTail n t)) = Lindeberg.mean μ f :=
    atc_tailCondLawFixedMarg μ hpos hμ1 σ hfC t s₁ m hst1 A
  have hm2 : (∫ B, φ₂ B ∂(ubfTail n t)) = Lindeberg.mean μ (Lindeberg.coord e) :=
    atc_tailCondLawFixedMarg μ hpos hμ1 σ
      (fun ω => GrandCoupling.abs_coord_le_one e ω) t s₂ m hst2 A
  rw [← hm1, ← hm2]
  exact hFKG


end AdaptDisintegration
end OSSS
end StatMech
