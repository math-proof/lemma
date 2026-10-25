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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part22
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


@[simp] lemma tripleRealizedSchedule_map_fst {R : Finset E} (S : TripleOrder R)
    (base : ConfigSpace E) :
    (tripleRealizedSchedule S base).map Prod.fst = realizedList S.leftOrder base := by
  induction S with
  | done => rfl
  | node e he mode closed opened ihc iho =>
      simp only [tripleRealizedSchedule, TripleOrder.leftOrder, realizedList, List.map_cons]
      split <;> simp_all

lemma tripleRealizedSchedule_mode {R : Finset E} (S : TripleOrder R)
    (base : ConfigSpace E) (p : E × TripleMode) (hp : p ∈ tripleRealizedSchedule S base) :
    p.2 = tripleModeAt S base p.1 := by
  induction S with
  | done => simp [tripleRealizedSchedule] at hp
  | @node R e he mode closed opened ihc iho =>
      by_cases hb : base e
      · simp only [tripleRealizedSchedule, hb, if_true, List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp [tripleModeAt]
        · have hz : p.1 ∈ realizedList opened.leftOrder base := by
            rw [← tripleRealizedSchedule_map_fst opened base]
            exact List.mem_map_of_mem hp
          have hne : p.1 ≠ e := by
            rw [← List.mem_toFinset, realizedList_toFinset] at hz
            exact (Finset.mem_erase.mp hz).1
          simp only [tripleModeAt, hne, if_false, hb, if_true]
          exact iho hp
      · simp only [tripleRealizedSchedule, hb, Bool.false_eq_true, if_false,
          List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp [tripleModeAt]
        · have hz : p.1 ∈ realizedList closed.leftOrder base := by
            rw [← tripleRealizedSchedule_map_fst closed base]
            exact List.mem_map_of_mem hp
          have hne : p.1 ≠ e := by
            rw [← List.mem_toFinset, realizedList_toFinset] at hz
            exact (Finset.mem_erase.mp hz).1
          simp only [tripleModeAt, hne, if_false, hb, Bool.false_eq_true]
          exact ihc hp

lemma idxOf_fst_tripleRealizedSchedule
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (p : E × TripleMode) (hp : p ∈ tripleRealizedSchedule S base) :
    (realizedList S.leftOrder base).idxOf p.1 = (tripleRealizedSchedule S base).idxOf p := by
  let l := tripleRealizedSchedule S base
  have hip : l.idxOf p < l.length := List.idxOf_lt_length_iff.mpr hp
  have hget : l.get ⟨l.idxOf p, hip⟩ = p := List.idxOf_get hip
  have hmap : (l.map Prod.fst).Nodup := by
    rw [show l.map Prod.fst = realizedList S.leftOrder base from
      tripleRealizedSchedule_map_fst S base]
    exact realizedList_nodup S.leftOrder base
  have hidx := List.get_idxOf hmap
    (⟨l.idxOf p, by simpa using hip⟩ : Fin (l.map Prod.fst).length)
  simp only [List.get_eq_getElem, List.getElem_map] at hidx
  rw [show l[l.idxOf p] = p from by simpa [List.get_eq_getElem] using hget] at hidx
  rw [show l.map Prod.fst = realizedList S.leftOrder base from
    tripleRealizedSchedule_map_fst S base] at hidx
  exact hidx

end AdaptiveCausalKernel
end OSSS
end StatMech
