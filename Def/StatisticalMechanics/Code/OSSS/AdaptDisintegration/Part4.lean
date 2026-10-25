/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptMConditional.Part6
import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part3
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


noncomputable def fiberStep (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (U : Fin n → ℝ) : ℝ :=
  ∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t+1)))
        - f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t))| ∂(Vcube n)


noncomputable def fiberDiag (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) (s : ℕ) (U : Fin n → ℝ) : ℝ :=
  ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s))
        * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)


noncomputable def fiberCross (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) (s₁ s₂ : ℕ) (U : Fin n → ℝ) : ℝ :=
  (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₁)) ∂(Vcube n))
    * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₂)) ∂(Vcube n))


def AdaptCondBBB (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    Prop :=
  ∀ (t : ℕ) (htn : t < n),
    let e := (σ : Fin n → E) ⟨t, htn⟩
    ((∫ U, fiberDiag μ σ f e t U * truncInd μ σ f U (t+1) ∂(Vcube n))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω)
            * ∫ U, truncInd μ σ f U (t+1) ∂(Vcube n))
    ∧ ((∫ U, fiberDiag μ σ f e (t+1) U * truncInd μ σ f U (t+1) ∂(Vcube n))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω)
            * ∫ U, truncInd μ σ f U (t+1) ∂(Vcube n))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
          * ∫ U, truncInd μ σ f U (t+1) ∂(Vcube n)
        ≤ ∫ U, fiberCross μ σ f e t (t+1) U * truncInd μ σ f U (t+1) ∂(Vcube n))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
          * ∫ U, truncInd μ σ f U (t+1) ∂(Vcube n)
        ≤ ∫ U, fiberCross μ σ f e (t+1) t U * truncInd μ σ f U (t+1) ∂(Vcube n))


end AdaptDisintegration
end OSSS
end StatMech
