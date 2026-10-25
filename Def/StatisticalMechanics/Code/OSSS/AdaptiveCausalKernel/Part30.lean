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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part29
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


noncomputable def targetIntegral (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base target : ConfigSpace E) : {R : Finset E} → CausalOrder R → ℝ
  | _, .done => 1
  | _, .node e _ active closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F target e
      (if active then
          (volume (thresholdInterval a false)).toReal *
            (volume (thresholdInterval q (target e))).toReal
        else
          (volume (thresholdInterval a false ∩ thresholdInterval q (target e))).toReal) *
          targetIntegral μ (insert e F) (Function.update base e false) target closed
        + (if active then
          (volume (thresholdInterval a true)).toReal *
            (volume (thresholdInterval q (target e))).toReal
        else
          (volume (thresholdInterval a true ∩ thresholdInterval q (target e))).toReal) *
          targetIntegral μ (insert e F) (Function.update base e true) target opened


end AdaptiveCausalKernel
end OSSS
end StatMech
