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
import Inductive.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part2
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


def TripleMode.leftIndependent : TripleMode → Bool
  | .before => true
  | .flip => false
  | .after => false

def TripleMode.rightIndependent : TripleMode → Bool
  | .before => true
  | .flip => true
  | .after => false

def TripleOrder.leftOrder : {R : Finset E} → TripleOrder R → CausalOrder R
  | _, .done => .done
  | _, .node e he mode closed opened =>
      .node e he mode.leftIndependent closed.leftOrder opened.leftOrder

def TripleOrder.rightOrder : {R : Finset E} → TripleOrder R → CausalOrder R
  | _, .done => .done
  | _, .node e he mode closed opened =>
      .node e he mode.rightIndependent closed.rightOrder opened.rightOrder


def tripleModeAt : {R : Finset E} → TripleOrder R →
    ConfigSpace E → E → TripleMode
  | _, .done, _, _ => .after
  | _, .node e _ mode closed opened, base, z =>
      if z = e then mode
      else if base e then tripleModeAt opened base z
      else tripleModeAt closed base z

end AdaptiveCausalKernel
end OSSS
end StatMech
