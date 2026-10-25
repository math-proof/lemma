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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part25
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


theorem crossScheduleProduct_eq_static (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base left right : ConfigSpace E)
    (schedule : List (E × TripleMode)) (hnd : (schedule.map Prod.fst).Nodup) :
    crossScheduleProduct μ F base left right schedule =
      staticCrossScheduleProduct μ F base left right schedule := by
  induction schedule generalizing F with
  | nil => rfl
  | cons p tail ih =>
      have hp : p.1 ∉ tail.map Prod.fst := (List.nodup_cons.mp hnd).1
      have htail : (tail.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      rw [crossScheduleProduct, staticCrossScheduleProduct, List.map_cons, List.prod_cons]
      simp only [List.idxOf_cons_self, List.take_zero, List.map_nil, List.toFinset_nil,
        Finset.union_empty]
      rw [ih (insert p.1 F) htail]
      unfold staticCrossScheduleProduct
      apply congrArg (fun z =>
        crossTripleWeight p.2 (condProbClosed μ F base p.1)
          (condProbClosed μ F left p.1) (condProbClosed μ F right p.1)
          (base p.1) (left p.1) (right p.1) * z)
      apply congrArg List.prod
      apply List.map_congr_left
      intro q hq
      have hpq : p ≠ q := by
        intro hpq
        subst q
        exact hp (List.mem_map_of_mem hq)
      rw [List.idxOf_cons_ne tail hpq]
      simp only [List.take_succ_cons, List.map_cons, List.toFinset_cons,
        Finset.union_insert, Finset.insert_union]

theorem crossTripleJointProb_eq_crossScheduleProduct (μ : ConfigSpace E → ℝ)
    (F : Finset E) (base left right : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) :
    crossTripleJointProb μ F base left right S =
      crossScheduleProduct μ F base left right (tripleRealizedSchedule S base) := by
  induction S generalizing F base with
  | done => rfl
  | @node R e he mode closed opened ihc iho =>
      rw [crossTripleJointProb, tripleRealizedSchedule, crossScheduleProduct]
      by_cases hb : base e
      · simp only [hb, if_true]
        exact congrArg
          (fun z => crossTripleWeight mode (condProbClosed μ F base e)
            (condProbClosed μ F left e) (condProbClosed μ F right e)
            true (left e) (right e) * z)
          (iho (insert e F) base)
      · simp only [hb, Bool.false_eq_true, if_false]
        exact congrArg
          (fun z => crossTripleWeight mode (condProbClosed μ F base e)
            (condProbClosed μ F left e) (condProbClosed μ F right e)
            false (left e) (right e) * z)
          (ihc (insert e F) base)

theorem staticCrossScheduleProduct_eq_prod_realized
    (μ : ConfigSpace E → ℝ) (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    staticCrossScheduleProduct μ ∅ base left right (tripleRealizedSchedule S base) =
      ∏ i : Fin (Fintype.card E),
        crossTripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
          (base (realizedEquiv S.leftOrder base i))
          (left (realizedEquiv S.leftOrder base i))
          (right (realizedEquiv S.leftOrder base i)) := by
  let schedule := tripleRealizedSchedule S base
  let sigma := realizedEquiv S.leftOrder base
  let g : E → ℝ := fun e =>
    crossTripleWeight (tripleModeAt S base e)
      (thr μ (sigma : Fin (Fintype.card E) → E) base (sigma.symm e))
      (thr μ (sigma : Fin (Fintype.card E) → E) left (sigma.symm e))
      (thr μ (sigma : Fin (Fintype.card E) → E) right (sigma.symm e))
      (base e) (left e) (right e)
  have hfac : (schedule.map fun p =>
      let before := ((schedule.take (schedule.idxOf p)).map Prod.fst).toFinset
      crossTripleWeight p.2 (condProbClosed μ before base p.1)
        (condProbClosed μ before left p.1) (condProbClosed μ before right p.1)
        (base p.1) (left p.1) (right p.1)).prod =
      (schedule.map fun p => g p.1).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    simp only
    rw [tripleRealizedSchedule_mode S base p hp]
    rw [← idxOf_fst_tripleRealizedSchedule S base p hp]
    rw [List.map_take]
    rw [show schedule.map Prod.fst = realizedList S.leftOrder base from
      tripleRealizedSchedule_map_fst S base]
    rw [← thr_realizedEquiv μ S.leftOrder base base p.1]
    rw [← thr_realizedEquiv μ S.leftOrder base left p.1]
    rw [← thr_realizedEquiv μ S.leftOrder base right p.1]
  unfold staticCrossScheduleProduct
  simp only [Finset.empty_union]
  rw [show tripleRealizedSchedule S base = schedule from rfl, hfac]
  rw [show (schedule.map fun p => g p.1) = (realizedList S.leftOrder base).map g from by
    change (tripleRealizedSchedule S base).map (g ∘ Prod.fst) =
      (realizedList S.leftOrder base).map g
    rw [← List.map_map, tripleRealizedSchedule_map_fst]]
  rw [← List.prod_toFinset g (realizedList_nodup S.leftOrder base)]
  rw [realizedList_toFinset]
  rw [← sigma.prod_comp g]
  apply Finset.prod_congr rfl
  intro i _
  simp [g, sigma]

theorem tripleLabelCube_frozenCrossRawAtom_toReal_eq_crossTripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    (tripleLabelCube (Fintype.card E)
      (frozenCrossRawAtom μ S base left right)).toReal =
        crossTripleJointProb μ ∅ base left right S := by
  rw [tripleLabelCube_frozenCrossRawAtom, ENNReal.toReal_prod]
  have hprod : (∏ i : Fin (Fintype.card E),
      ((((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (crossRawTriple μ S base left right i)).toReal) =
      ∏ i : Fin (Fintype.card E),
        crossTripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
          (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
          (base (realizedEquiv S.leftOrder base i))
          (left (realizedEquiv S.leftOrder base i))
          (right (realizedEquiv S.leftOrder base i)) := by
    apply Finset.prod_congr rfl
    intro i _
    exact crossRawTriple_toReal_eq_crossTripleWeight μ hpos S base left right i
  rw [hprod]
  rw [← staticCrossScheduleProduct_eq_prod_realized μ S base left right]
  rw [← crossScheduleProduct_eq_static μ ∅ base left right
    (tripleRealizedSchedule S base) (by
      rw [tripleRealizedSchedule_map_fst]
      exact realizedList_nodup S.leftOrder base)]
  exact (crossTripleJointProb_eq_crossScheduleProduct μ ∅ base left right S).symm


theorem tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    (tripleCube (Fintype.card E)
      (frozenCrossCodeAtom μ S base left right)).toReal =
      crossTripleJointProb μ ∅ base left right S := by
  rw [frozenCrossCodeAtom_eq_rawTripleBox]
  exact tripleLabelCube_frozenCrossRawAtom_toReal_eq_crossTripleJointProb
    μ hpos S base left right


end AdaptiveCausalKernel
end OSSS
end StatMech
