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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part24
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


@[simp] lemma flipTripleProb_beforeOfCausal
    (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) (z : E) {R : Finset E}
    (S : CausalOrder R) :
    flipTripleProb μ F base left right z (TripleOrder.beforeOfCausal S) = 0 := by
  induction S generalizing F base with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      by_cases hze : z = e
      · subst z
        simp [flipTripleProb, TripleOrder.beforeOfCausal]
      · simp [flipTripleProb, TripleOrder.beforeOfCausal, hze, ihc, iho]

@[simp] lemma flipCrossTripleProb_beforeOfCausal
    (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base left right : ConfigSpace E) (z : E) {R : Finset E}
    (S : CausalOrder R) :
    flipCrossTripleProb μ F base left right z (TripleOrder.beforeOfCausal S) = 0 := by
  induction S generalizing F base with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      by_cases hze : z = e
      · subst z
        simp [flipCrossTripleProb, TripleOrder.beforeOfCausal]
      · simp [flipCrossTripleProb, TripleOrder.beforeOfCausal, hze, ihc, iho]

@[simp] lemma flipBaseProb_beforeOfCausal
    (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base : ConfigSpace E) (z : E) {R : Finset E} (S : CausalOrder R) :
    flipBaseProb μ F base z (TripleOrder.beforeOfCausal S) = 0 := by
  induction S generalizing F base with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      by_cases hze : z = e
      · subst z
        simp [flipBaseProb, TripleOrder.beforeOfCausal]
      · simp [flipBaseProb, TripleOrder.beforeOfCausal, hze, ihc, iho]

@[simp] theorem flipTripleProb_extendDecisionTreeTriple_none
    (μ : ConfigSpace E → ℝ) (F : Finset E) (T : DecisionTree E)
    (known base left right : ConfigSpace E) (R : Finset E) (z : E) :
    flipTripleProb μ F base left right z
      (extendDecisionTreeTriple none T known R) = 0 := by
  induction T generalizing F known base R with
  | leaf b => simp [extendDecisionTreeTriple]
  | node e opened closed iho ihc =>
      rw [extendDecisionTreeTriple]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        by_cases hze : z = e
        · subst z
          simp [flipTripleProb]
        · simp [flipTripleProb, hze, ihc, iho]
      · rw [dif_neg he]
        by_cases hb : known e
        · simp [hb, iho]
        · simp [hb, ihc]

@[simp] theorem flipCrossTripleProb_extendDecisionTreeTriple_none
    (μ : ConfigSpace E → ℝ) (F : Finset E) (T : DecisionTree E)
    (known base left right : ConfigSpace E) (R : Finset E) (z : E) :
    flipCrossTripleProb μ F base left right z
      (extendDecisionTreeTriple none T known R) = 0 := by
  induction T generalizing F known base R with
  | leaf b => simp [extendDecisionTreeTriple]
  | node e opened closed iho ihc =>
      rw [extendDecisionTreeTriple]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        by_cases hze : z = e
        · subst z
          simp [flipCrossTripleProb]
        · simp [flipCrossTripleProb, hze, ihc, iho]
      · rw [dif_neg he]
        by_cases hb : known e
        · simp [hb, iho]
        · simp [hb, ihc]

@[simp] theorem flipBaseProb_extendDecisionTreeTriple_none
    (μ : ConfigSpace E → ℝ) (F : Finset E) (T : DecisionTree E)
    (known base : ConfigSpace E) (R : Finset E) (z : E) :
    flipBaseProb μ F base z (extendDecisionTreeTriple none T known R) = 0 := by
  induction T generalizing F known base R with
  | leaf b => simp [extendDecisionTreeTriple]
  | node e opened closed iho ihc =>
      rw [extendDecisionTreeTriple]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        by_cases hze : z = e
        · subst z
          simp [flipBaseProb]
        · simp [flipBaseProb, hze, ihc, iho]
      · rw [dif_neg he]
        by_cases hb : known e
        · simp [hb, iho]
        · simp [hb, ihc]

end AdaptiveCausalKernel
end OSSS
end StatMech
