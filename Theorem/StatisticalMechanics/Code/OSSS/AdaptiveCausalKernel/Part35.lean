/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part35
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace OSSS

namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem decisionTree_branch_adapt_step_fiber_le {μ : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < μ ω) (hmono : IsMonotonicMeasure μ) (T : DecisionTree E)
    (base : ConfigSpace E) {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf) (t : ℕ) (ht : 1 ≤ t)
    (htm : t ≤ (T.queried base).card) (htn : t - 1 < Fintype.card E)
    (U : Fin (Fintype.card E) → ℝ) :
    let S := extendDecisionTree T base (Finset.univ : Finset E)
    let σ := realizedEquiv S base
    let m := (T.queried base).card
    let e := (σ : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩
    fiberAdaptAbsStep μ σ f U m t
      ≤ fiberAdaptObservable μ σ (fun ω => f ω * Lindeberg.coord e ω) U m (t - 1)
        + fiberAdaptObservable μ σ (fun ω => f ω * Lindeberg.coord e ω) U m t
        - fiberAdaptObservable μ σ f U m (t - 1)
            * fiberAdaptObservable μ σ (Lindeberg.coord e) U m t
        - fiberAdaptObservable μ σ f U m t
            * fiberAdaptObservable μ σ (Lindeberg.coord e) U m (t - 1) := by
  dsimp only
  unfold fiberAdaptAbsStep fiberAdaptObservable
  exact AdaptDisintegration.adsD_adapt_step_fiber_le hpos hmono _ hf hfC t _ ht htm htn U

end AdaptiveCausalKernel
end OSSS
end StatMech
