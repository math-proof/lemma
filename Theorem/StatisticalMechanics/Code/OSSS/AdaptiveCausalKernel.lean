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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel
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


lemma realizedList_toFinset {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : (realizedList S base).toFinset = R := by
  induction S with
  | done => rfl
  | @node R e he independent closed opened ihc iho =>
      by_cases hb : base e
      · simp only [realizedList, hb, if_true, List.toFinset_cons]
        rw [iho, Finset.insert_erase he]
      · simp only [realizedList, hb, Bool.false_eq_true, if_false, List.toFinset_cons]
        rw [ihc, Finset.insert_erase he]


lemma realizedList_nodup {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : (realizedList S base).Nodup := by
  induction S with
  | done => simp [realizedList]
  | @node R e he independent closed opened ihc iho =>
      by_cases hb : base e
      · simp only [realizedList, hb, if_true, List.nodup_cons]
        refine ⟨?_, iho⟩
        rw [← List.mem_toFinset, realizedList_toFinset]
        simp
      · simp only [realizedList, hb, Bool.false_eq_true, if_false, List.nodup_cons]
        refine ⟨?_, ihc⟩
        rw [← List.mem_toFinset, realizedList_toFinset]
        simp

lemma realizedList_length {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : (realizedList S base).length = R.card := by
  rw [← List.toFinset_card_of_nodup (realizedList_nodup S base),
    realizedList_toFinset]


end AdaptiveCausalKernel
end OSSS
end StatMech
