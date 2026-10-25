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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part11
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


noncomputable def sharedAtIndicator (T : DecisionTree E) (base : ConfigSpace E)
    (t : ℕ) (e : E) : ℝ :=
  if e ∈ sharedEdges
      (extendDecisionTreeAt t T base (Finset.univ : Finset E)) base then 1 else 0


noncomputable def sharedStepIndicator (T : DecisionTree E) (base : ConfigSpace E)
    (t : ℕ) (e : E) : ℝ :=
  sharedAtIndicator T base t e - sharedAtIndicator T base (t + 1) e

end AdaptiveCausalKernel
end OSSS
end StatMech
