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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part27
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


@[simp] lemma realizedSchedule_map_fst {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) :
    (realizedSchedule S base).map Prod.fst = realizedList S base := by
  induction S with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      simp only [realizedSchedule, List.map_cons, realizedList]
      split <;> simp_all

lemma realizedSchedule_length {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : (realizedSchedule S base).length = R.card := by
  rw [← realizedList_length S base, ← realizedSchedule_map_fst S base,
    List.length_map]

lemma realizedSchedule_mode {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) (p : E × Bool) (hp : p ∈ realizedSchedule S base) :
    p.2 = independentAt S base p.1 := by
  induction S with
  | done => simp [realizedSchedule] at hp
  | @node R e he independent closed opened ihc iho =>
      by_cases hb : base e
      · simp only [realizedSchedule, hb, if_true, List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp [independentAt]
        · have hz : p.1 ∈ realizedList opened base := by
            rw [← realizedSchedule_map_fst opened base]
            exact List.mem_map_of_mem hp
          have hne : p.1 ≠ e := by
            rw [← List.mem_toFinset, realizedList_toFinset] at hz
            exact (Finset.mem_erase.mp hz).1
          simp only [independentAt, hne, if_false, hb, if_true]
          exact iho hp
      · simp only [realizedSchedule, hb, Bool.false_eq_true, if_false, List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp [independentAt]
        · have hz : p.1 ∈ realizedList closed base := by
            rw [← realizedSchedule_map_fst closed base]
            exact List.mem_map_of_mem hp
          have hne : p.1 ≠ e := by
            rw [← List.mem_toFinset, realizedList_toFinset] at hz
            exact (Finset.mem_erase.mp hz).1
          simp only [independentAt, hne, if_false, hb, Bool.false_eq_true]
          exact ihc hp

lemma idxOf_fst_realizedSchedule (S : CausalOrder (Finset.univ : Finset E))
    (base : ConfigSpace E) (p : E × Bool) (hp : p ∈ realizedSchedule S base) :
    (realizedList S base).idxOf p.1 = (realizedSchedule S base).idxOf p := by
  let l := realizedSchedule S base
  have hip : l.idxOf p < l.length := List.idxOf_lt_length_iff.mpr hp
  have hget : l.get ⟨l.idxOf p, hip⟩ = p := List.idxOf_get hip
  have hmap : (l.map Prod.fst).Nodup := by
    rw [show l.map Prod.fst = realizedList S base from realizedSchedule_map_fst S base]
    exact realizedList_nodup S base
  have hidx := List.get_idxOf hmap
    (⟨l.idxOf p, by simpa using hip⟩ : Fin (l.map Prod.fst).length)
  simp only [List.get_eq_getElem, List.getElem_map] at hidx
  rw [show l[l.idxOf p] = p from by simpa [List.get_eq_getElem] using hget] at hidx
  rw [show l.map Prod.fst = realizedList S base from realizedSchedule_map_fst S base] at hidx
  exact hidx


end AdaptiveCausalKernel
end OSSS
end StatMech
