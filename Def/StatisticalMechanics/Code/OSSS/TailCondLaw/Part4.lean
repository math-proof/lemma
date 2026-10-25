/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptCondReduction
import Theorem.StatisticalMechanics.Code.OSSS.TailCondLaw.Part4
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


def atc_TailCondLawFixed (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) : Prop :=
  ∀ (t : ℕ) (htn : t < n) (m : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ),
    let e := (σ : Fin n → E) ⟨t, htn⟩
    ((∫ B, atc_fiberDiagFixed μ σ f e m t (acp_join t A B) ∂(ubfTail n t))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω))
    ∧ ((∫ B, atc_fiberDiagFixed μ σ f e m (t+1) (acp_join t A B) ∂(ubfTail n t))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
        ≤ ∫ B, atc_fiberCrossFixed μ σ f e m t (t+1) (acp_join t A B) ∂(ubfTail n t))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
        ≤ ∫ B, atc_fiberCrossFixed μ σ f e m (t+1) t (acp_join t A B) ∂(ubfTail n t))


end AdaptDisintegration
end OSSS
end StatMech
