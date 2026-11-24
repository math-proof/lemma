module
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
public import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part26
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


def realizedSchedule : {R : Finset E} → CausalOrder R →
    ConfigSpace E → List (E × Bool)
  | _, .done, _ => []
  | _, .node e _ independent closed opened, base =>
      (e, independent) :: if base e then realizedSchedule opened base
        else realizedSchedule closed base

end AdaptiveCausalKernel
end OSSS
end StatMech
