module
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
public import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Inductive.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel
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


def realizedList : {R : Finset E} → CausalOrder R → ConfigSpace E → List E
  | _, .done, _ => []
  | _, .node e _ _ closed opened, base =>
      if base e then e :: realizedList opened base
      else e :: realizedList closed base


end AdaptiveCausalKernel
end OSSS
end StatMech
