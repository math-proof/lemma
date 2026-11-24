module
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
public import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part33
open scoped BigOperators
open MeasureTheory
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace OSSS

namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def fiberAbsStep (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (t : ℕ) : ℝ :=
  ∫ V, |f (codeMap μ (σ : Fin n → E) (GrandCoupling.Wt U V t))
      - f (codeMap μ (σ : Fin n → E) (GrandCoupling.Wt U V (t - 1)))|
    ∂(GrandCoupling.Vcube n)

noncomputable def fiberObservable (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) (U : Fin n → ℝ) (s : ℕ) : ℝ :=
  ∫ V, g (codeMap μ (σ : Fin n → E) (GrandCoupling.Wt U V s))
    ∂(GrandCoupling.Vcube n)


end AdaptiveCausalKernel
end OSSS
end StatMech
