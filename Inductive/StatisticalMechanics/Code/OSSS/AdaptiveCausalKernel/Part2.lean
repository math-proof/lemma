/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
public import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part4
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


public inductive TripleMode where
  | before
  | flip
  | after
  deriving DecidableEq


public inductive TripleOrder : Finset E → Type _
  | done : TripleOrder ∅
  | node {R : Finset E} (e : E) (he : e ∈ R) (mode : TripleMode)
      (closed opened : TripleOrder (R.erase e)) : TripleOrder R

end AdaptiveCausalKernel
end OSSS
end StatMech
