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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part26
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


theorem jointProb_allIndependent_eq_mul_pathProb (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base target : ConfigSpace E) {R : Finset E}
    (S : CausalOrder R) :
    jointProb μ F base target (allIndependent S) =
      pathProb μ F base base S * pathProb μ F base target S := by
  induction S generalizing F with
  | done =>
      change (1 : ℝ) = 1 * 1
      ring
  | node e he independent closed opened ihc iho =>
      by_cases hb : base e
      · simp only [allIndependent, jointProb, pathProb, hb, if_true,
          splitWeight, independentWeight]
        rw [iho]
        ring
      · simp only [allIndependent, jointProb, pathProb, hb,
          Bool.false_eq_true, if_false, splitWeight, independentWeight]
        rw [ihc]
        simp only [if_true]
        ring


end AdaptiveCausalKernel
end OSSS
end StatMech
