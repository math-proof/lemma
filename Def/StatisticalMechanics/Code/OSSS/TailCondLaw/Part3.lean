/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptCondReduction
import Theorem.StatisticalMechanics.Code.OSSS.TailCondLaw.Part3
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


noncomputable def atc_fiberCrossFixed (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) (m s₁ s₂ : ℕ) (U : Fin n → ℝ) : ℝ :=
  (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁)) ∂(Vcube n))
    * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂)) ∂(Vcube n))


end AdaptDisintegration
end OSSS
end StatMech
