module
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
public import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part15
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


def splitWeight (independent : Bool) (a q : ℝ) (base target : Bool) : ℝ :=
  if independent then independentWeight a q base target else overlapWeight a q base target

def thresholdInterval (q : ℝ) (b : Bool) : Set ℝ :=
  if b then Set.Ico q 1 else Set.Ico 0 q

end AdaptiveCausalKernel
end OSSS
end StatMech
