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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part13
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


theorem sharedStepIndicator_eq_tripleFlipIndicator
    (T : DecisionTree E) (base : ConfigSpace E) (t : ℕ) (e : E) :
    sharedStepIndicator T base t e =
      tripleFlipIndicator
        (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e := by
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)
  unfold sharedStepIndicator sharedAtIndicator tripleFlipIndicator
  rw [← extendDecisionTreeTriple_leftOrder t T base Finset.univ]
  rw [← extendDecisionTreeTriple_rightOrder t T base Finset.univ]
  change (if e ∈ sharedEdges S.leftOrder base then 1 else 0) -
      (if e ∈ sharedEdges S.rightOrder base then 1 else 0) =
    if tripleModeAt S base e = TripleMode.flip then 1 else 0
  simp only [mem_sharedEdges_iff_independentAt_false S.leftOrder base e (by simp),
    mem_sharedEdges_iff_independentAt_false S.rightOrder base e (by simp)]
  rw [independentAt_leftOrder, independentAt_rightOrder]
  cases tripleModeAt S base e <;>
    simp [TripleMode.leftIndependent, TripleMode.rightIndependent]


end AdaptiveCausalKernel
end OSSS
end StatMech
