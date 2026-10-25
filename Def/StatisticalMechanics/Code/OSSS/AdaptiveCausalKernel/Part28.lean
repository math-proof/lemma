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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part27
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


noncomputable def scheduleProduct (μ : ConfigSpace E → ℝ) :
    Finset E → ConfigSpace E → ConfigSpace E → List (E × Bool) → ℝ
  | _, _, _, [] => 1
  | F, base, target, (e, independent) :: tail =>
      splitWeight independent (condProbClosed μ F base e)
          (condProbClosed μ F target e) (base e) (target e) *
        scheduleProduct μ (insert e F) base target tail


noncomputable def staticScheduleProduct (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base target : ConfigSpace E) (schedule : List (E × Bool)) : ℝ :=
  (schedule.map fun p =>
    let before := F ∪ ((schedule.take (schedule.idxOf p)).map Prod.fst).toFinset
    splitWeight p.2 (condProbClosed μ before base p.1)
      (condProbClosed μ before target p.1) (base p.1) (target p.1)).prod


end AdaptiveCausalKernel
end OSSS
end StatMech
