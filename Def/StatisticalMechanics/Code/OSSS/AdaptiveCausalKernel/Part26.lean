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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part25
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


noncomputable def targetProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base target : ConfigSpace E) : {R : Finset E} → CausalOrder R → ℝ
  | _, .done => 1
  | _, .node e _ active closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F target e
      splitWeight active a q false (target e) *
          targetProb μ (insert e F) (Function.update base e false) target closed
        + splitWeight active a q true (target e) *
          targetProb μ (insert e F) (Function.update base e true) target opened


noncomputable def jointProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base target : ConfigSpace E) : {R : Finset E} → CausalOrder R → ℝ
  | _, .done => 1
  | _, .node e _ independent closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F target e
      if base e then
        splitWeight independent a q true (target e) *
          jointProb μ (insert e F) base target opened
      else
        splitWeight independent a q false (target e) *
          jointProb μ (insert e F) base target closed


noncomputable def pathProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (driver target : ConfigSpace E) : {R : Finset E} → CausalOrder R → ℝ
  | _, .done => 1
  | _, .node e _ _ closed opened =>
      bitWeight (condProbClosed μ F target e) (target e) *
        if driver e then
          pathProb μ (insert e F) driver target opened
        else pathProb μ (insert e F) driver target closed


end AdaptiveCausalKernel
end OSSS
end StatMech
