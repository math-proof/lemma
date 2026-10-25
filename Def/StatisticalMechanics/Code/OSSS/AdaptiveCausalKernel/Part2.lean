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
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel
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


noncomputable def realizedEquiv
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    Fin (Fintype.card E) ≃ E := by
  let l := realizedList S base
  have hnd : l.Nodup := realizedList_nodup S base
  have hall : ∀ e : E, e ∈ l := by
    intro e
    rw [← List.mem_toFinset, realizedList_toFinset]
    exact Finset.mem_univ e
  have hlen : l.length = Fintype.card E := by
    calc
      l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ = (Finset.univ : Finset E).card := by
        rw [show l = realizedList S base from rfl, realizedList_toFinset]
      _ = Fintype.card E := Finset.card_univ
  exact (finCongr hlen.symm).trans (hnd.getEquivOfForallMemList l hall)

end AdaptiveCausalKernel
end OSSS
end StatMech
