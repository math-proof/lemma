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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part28
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


theorem scheduleProduct_eq_staticScheduleProduct (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base target : ConfigSpace E) (schedule : List (E × Bool))
    (hnd : (schedule.map Prod.fst).Nodup) :
    scheduleProduct μ F base target schedule =
      staticScheduleProduct μ F base target schedule := by
  induction schedule generalizing F with
  | nil => rfl
  | cons p tail ih =>
      have hp : p.1 ∉ tail.map Prod.fst := (List.nodup_cons.mp hnd).1
      have htail : (tail.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      rw [scheduleProduct, staticScheduleProduct, List.map_cons, List.prod_cons]
      simp only [List.idxOf_cons_self, List.take_zero, List.map_nil, List.toFinset_nil,
        Finset.union_empty]
      rw [ih (insert p.1 F) htail]
      unfold staticScheduleProduct
      apply congrArg (fun x : ℝ =>
        splitWeight p.2 (condProbClosed μ F base p.1)
          (condProbClosed μ F target p.1) (base p.1) (target p.1) * x)
      apply congrArg List.prod
      apply List.map_congr_left
      intro q hq
      have hpq : p ≠ q := by
        intro hpq
        subst q
        exact hp (List.mem_map_of_mem hq)
      have hcoord : p.1 ≠ q.1 := by
        intro heq
        have hmem : q.1 ∈ tail.map Prod.fst := by
          rw [List.mem_map]
          exact ⟨q, hq, rfl⟩
        exact hp (heq ▸ hmem)
      rw [List.idxOf_cons_ne tail hpq]
      simp only [List.take_succ_cons, List.map_cons, List.toFinset_cons,
        Finset.union_insert, Finset.insert_union]

theorem staticScheduleProduct_eq_prod_realized (μ : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E)) (base target : ConfigSpace E) :
    staticScheduleProduct μ ∅ base target (realizedSchedule S base) =
      ∏ i : Fin (Fintype.card E),
        splitWeight (independentAt S base (realizedEquiv S base i))
          (thr μ (realizedEquiv S base : Fin (Fintype.card E) → E) base i)
          (thr μ (realizedEquiv S base : Fin (Fintype.card E) → E) target i)
          (base (realizedEquiv S base i)) (target (realizedEquiv S base i)) := by
  let schedule := realizedSchedule S base
  let σ := realizedEquiv S base
  let g : E → ℝ := fun e =>
    splitWeight (independentAt S base e)
      (thr μ (σ : Fin (Fintype.card E) → E) base (σ.symm e))
      (thr μ (σ : Fin (Fintype.card E) → E) target (σ.symm e))
      (base e) (target e)
  have hfac : (schedule.map fun p =>
      let before := ((schedule.take (schedule.idxOf p)).map Prod.fst).toFinset
      splitWeight p.2 (condProbClosed μ before base p.1)
        (condProbClosed μ before target p.1) (base p.1) (target p.1)).prod =
      (schedule.map fun p => g p.1).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    simp only
    rw [realizedSchedule_mode S base p hp]
    rw [← idxOf_fst_realizedSchedule S base p hp]
    rw [List.map_take]
    rw [show schedule.map Prod.fst = realizedList S base from
      realizedSchedule_map_fst S base]
    change
      splitWeight (independentAt S base p.1)
          (condProbClosed μ
            ((realizedList S base).take ((realizedList S base).idxOf p.1)).toFinset
            base p.1)
          (condProbClosed μ
            ((realizedList S base).take ((realizedList S base).idxOf p.1)).toFinset
            target p.1) (base p.1) (target p.1) = g p.1
    rw [← thr_realizedEquiv μ S base base p.1]
    rw [← thr_realizedEquiv μ S base target p.1]
  unfold staticScheduleProduct
  simp only [Finset.empty_union]
  rw [show realizedSchedule S base = schedule from rfl, hfac]
  rw [show (schedule.map fun p => g p.1) = (realizedList S base).map g from by
    change (realizedSchedule S base).map (g ∘ Prod.fst) =
      (realizedList S base).map g
    rw [← List.map_map, realizedSchedule_map_fst]]
  rw [← List.prod_toFinset g (realizedList_nodup S base)]
  rw [realizedList_toFinset]
  rw [← σ.prod_comp g]
  apply Finset.prod_congr rfl
  intro i _
  simp [g, σ]


theorem jointProb_eq_scheduleProduct (μ : ConfigSpace E → ℝ) (F : Finset E)
    (base target : ConfigSpace E) {R : Finset E} (S : CausalOrder R) :
    jointProb μ F base target S =
      scheduleProduct μ F base target (realizedSchedule S base) := by
  induction S generalizing F base with
  | done => rfl
  | @node R e he independent closed opened ihc iho =>
      rw [jointProb, realizedSchedule, scheduleProduct]
      by_cases hb : base e
      · simp only [hb, if_true]
        exact congrArg
          (fun z => splitWeight independent (condProbClosed μ F base e)
            (condProbClosed μ F target e) true (target e) * z)
          (iho (insert e F) base)
      · simp only [hb, Bool.false_eq_true, if_false]
        exact congrArg
          (fun z => splitWeight independent (condProbClosed μ F base e)
            (condProbClosed μ F target e) false (target e) * z)
          (ihc (insert e F) base)


theorem pairedCube_frozenCodeAtom_toReal_eq_jointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) :
    (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal =
      jointProb μ ∅ base target S := by
  rw [pairedCube_frozenCodeAtom_toReal_eq_prod_splitWeight μ hpos S base target]
  rw [← staticScheduleProduct_eq_prod_realized μ S base target]
  rw [← scheduleProduct_eq_staticScheduleProduct μ ∅ base target
    (realizedSchedule S base) (by
      rw [realizedSchedule_map_fst]
      exact realizedList_nodup S base)]
  exact (jointProb_eq_scheduleProduct μ ∅ base target S).symm


theorem pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    (pairedCube (Fintype.card E)
      (frozenTripleCodeAtom μ S base left right)).toReal =
      tripleJointProb μ ∅ base left right S := by
  rw [pairedCube_frozenTripleCodeAtom_toReal_eq_prod_tripleWeight
    μ hpos S base left right]
  rw [← staticTripleScheduleProduct_eq_prod_realized μ S base left right]
  rw [← tripleScheduleProduct_eq_static μ ∅ base left right
    (tripleRealizedSchedule S base) (by
      rw [tripleRealizedSchedule_map_fst]
      exact realizedList_nodup S.leftOrder base)]
  exact (tripleJointProb_eq_tripleScheduleProduct μ ∅ base left right S).symm

end AdaptiveCausalKernel
end OSSS
end StatMech
