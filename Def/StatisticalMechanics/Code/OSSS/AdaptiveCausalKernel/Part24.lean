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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part23
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


noncomputable def crossTripleProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) : {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 1
  | _, .node e _ mode closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F right e
      crossTripleWeight mode a q r false (left e) (right e) *
          crossTripleProb μ (insert e F) (Function.update base e false) left right closed
        + crossTripleWeight mode a q r true (left e) (right e) *
          crossTripleProb μ (insert e F) (Function.update base e true) left right opened

noncomputable def crossTripleJointProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) : {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 1
  | _, .node e _ mode closed opened =>
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F right e
      if base e then
        crossTripleWeight mode a q r true (left e) (right e) *
          crossTripleJointProb μ (insert e F) base left right opened
      else
        crossTripleWeight mode a q r false (left e) (right e) *
          crossTripleJointProb μ (insert e F) base left right closed


noncomputable def flipTripleProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) (z : E) :
    {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 0
  | _, .node e he mode closed opened =>
      if z = e then
        if mode = .flip then
          tripleProb μ F base left right (.node e he mode closed opened)
        else 0
      else
        let a := condProbClosed μ F base e
        let q := condProbClosed μ F left e
        let r := condProbClosed μ F right e
        tripleWeight mode a q r false (left e) (right e) *
            flipTripleProb μ (insert e F) (Function.update base e false)
              left right z closed
          + tripleWeight mode a q r true (left e) (right e) *
            flipTripleProb μ (insert e F) (Function.update base e true)
              left right z opened


noncomputable def flipCrossTripleProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) (z : E) :
    {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 0
  | _, .node e he mode closed opened =>
      if z = e then
        if mode = .flip then
          crossTripleProb μ F base left right (.node e he mode closed opened)
        else 0
      else
        let a := condProbClosed μ F base e
        let q := condProbClosed μ F left e
        let r := condProbClosed μ F right e
        crossTripleWeight mode a q r false (left e) (right e) *
            flipCrossTripleProb μ (insert e F) (Function.update base e false)
              left right z closed
          + crossTripleWeight mode a q r true (left e) (right e) *
            flipCrossTripleProb μ (insert e F) (Function.update base e true)
              left right z opened


noncomputable def flipBaseProb (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base : ConfigSpace E) (z : E) : {R : Finset E} → TripleOrder R → ℝ
  | _, .done => 0
  | _, .node e _ mode closed opened =>
      if z = e then
        if mode = .flip then 1 else 0
      else
        let a := condProbClosed μ F base e
        bitWeight a false *
            flipBaseProb μ (insert e F) (Function.update base e false) z closed
          + bitWeight a true *
            flipBaseProb μ (insert e F) (Function.update base e true) z opened

end AdaptiveCausalKernel
end OSSS
end StatMech
