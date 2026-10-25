/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptCondBBProof2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.UBlockFactor
import Theorem.StatisticalMechanics.Code.OSSS.AdaptCondBBProof2.Part2
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


noncomputable def acp_join {n : ℕ} (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) : Fin n → ℝ :=
  (ubfSplit n t).symm (A, B)


def acp_TailCondLaw (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    Prop :=
  ∀ (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ),
    let e := (σ : Fin n → E) ⟨t, htn⟩
    ((∫ B, fiberDiag μ σ f e t (acp_join t A B) ∂(ubfTail n t))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω))
    ∧ ((∫ B, fiberDiag μ σ f e (t+1) (acp_join t A B) ∂(ubfTail n t))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
        ≤ ∫ B, fiberCross μ σ f e t (t+1) (acp_join t A B) ∂(ubfTail n t))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
        ≤ ∫ B, fiberCross μ σ f e (t+1) t (acp_join t A B) ∂(ubfTail n t))

end AdaptDisintegration
end OSSS
end StatMech
