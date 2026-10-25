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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part21
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


noncomputable def tripleProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) : {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 1
  | _, .node e he mode closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F right e
      tripleWeight mode a q r false (left e) (right e) *
          tripleProb μ (insert e F) (Function.update base e false) left right closed
        + tripleWeight mode a q r true (left e) (right e) *
          tripleProb μ (insert e F) (Function.update base e true) left right opened

noncomputable def tripleJointProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) : {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 1
  | _, .node e he mode closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F right e
      if base e then
        tripleWeight mode a q r true (left e) (right e) *
          tripleJointProb μ (insert e F) base left right opened
      else
        tripleWeight mode a q r false (left e) (right e) *
          tripleJointProb μ (insert e F) base left right closed

def tripleRealizedSchedule : {R : Finset E} → TripleOrder R →
    ConfigSpace E → List (E × TripleMode)
  | _, .done, _ => []
  | _, .node e _ mode closed opened, base =>
      (e, mode) :: if base e then tripleRealizedSchedule opened base
        else tripleRealizedSchedule closed base

end AdaptiveCausalKernel
end OSSS
end StatMech
