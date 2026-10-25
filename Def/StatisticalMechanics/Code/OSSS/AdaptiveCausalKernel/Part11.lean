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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part10
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


noncomputable def extendDecisionTreeAt :
    ℕ → DecisionTree E → ConfigSpace E → (R : Finset E) → CausalOrder R
  | _, .leaf _, _, R => fixedOrder R
  | t, .node e opened closed, known, R =>
      if he : e ∈ R then
        CausalOrder.node e he (decide (0 < t))
          (extendDecisionTreeAt (t - 1) closed
            (Function.update known e false) (R.erase e))
          (extendDecisionTreeAt (t - 1) opened
            (Function.update known e true) (R.erase e))
      else if known e then extendDecisionTreeAt t opened known R
      else extendDecisionTreeAt t closed known R

end AdaptiveCausalKernel
end OSSS
end StatMech
