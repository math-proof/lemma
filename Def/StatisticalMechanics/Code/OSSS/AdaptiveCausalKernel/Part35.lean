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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part34
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


noncomputable def fiberAdaptAbsStep (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (m t : ℕ) : ℝ :=
  ∫ V, |f (codeMap μ (σ : Fin n → E) (AdaptMConditional.adaptWt U V m t))
      - f (codeMap μ (σ : Fin n → E)
          (AdaptMConditional.adaptWt U V m (t - 1)))| ∂(GrandCoupling.Vcube n)

noncomputable def fiberAdaptObservable (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) (U : Fin n → ℝ) (m s : ℕ) : ℝ :=
  ∫ V, g (codeMap μ (σ : Fin n → E) (AdaptMConditional.adaptWt U V m s))
    ∂(GrandCoupling.Vcube n)


end AdaptiveCausalKernel
end OSSS
end StatMech
