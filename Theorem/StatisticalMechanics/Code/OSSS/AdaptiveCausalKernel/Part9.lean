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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part9
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


@[simp] lemma TripleOrder.leftOrder_beforeOfCausal {R : Finset E}
    (S : CausalOrder R) : (TripleOrder.beforeOfCausal S).leftOrder = allIndependent S := by
  induction S with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      simp only [TripleOrder.beforeOfCausal, TripleOrder.leftOrder,
        TripleMode.leftIndependent, allIndependent]
      rw [ihc, iho]

@[simp] lemma TripleOrder.rightOrder_beforeOfCausal {R : Finset E}
    (S : CausalOrder R) : (TripleOrder.beforeOfCausal S).rightOrder = allIndependent S := by
  induction S with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      simp only [TripleOrder.beforeOfCausal, TripleOrder.rightOrder,
        TripleMode.rightIndependent, allIndependent]
      rw [ihc, iho]


end AdaptiveCausalKernel
end OSSS
end StatMech
