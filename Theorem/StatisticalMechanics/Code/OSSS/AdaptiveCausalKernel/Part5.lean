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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part5
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


lemma realizedList_leftOrder_eq_rightOrder {R : Finset E} (S : TripleOrder R)
    (base : ConfigSpace E) :
    realizedList S.leftOrder base = realizedList S.rightOrder base := by
  induction S with
  | done => rfl
  | node e he mode closed opened ihc iho =>
      simp only [TripleOrder.leftOrder, TripleOrder.rightOrder, realizedList]
      split <;> simp_all

lemma realizedEquiv_leftOrder_eq_rightOrder
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    realizedEquiv S.leftOrder base = realizedEquiv S.rightOrder base := by
  apply Equiv.ext
  intro i
  apply (realizedEquiv S.rightOrder base).symm.injective
  apply Fin.ext
  rw [Equiv.symm_apply_apply]
  rw [realizedEquiv_symm_val]
  rw [← realizedList_leftOrder_eq_rightOrder S base]
  rw [← realizedEquiv_symm_val]
  simp

lemma independentAt_leftOrder {R : Finset E} (S : TripleOrder R)
    (base : ConfigSpace E) (z : E) :
    independentAt S.leftOrder base z = (tripleModeAt S base z).leftIndependent := by
  induction S with
  | done => rfl
  | @node R e he mode closed opened ihc iho =>
      simp only [TripleOrder.leftOrder, independentAt, tripleModeAt]
      by_cases hze : z = e
      · simp [hze]
      · simp only [hze, if_false]
        split <;> assumption

lemma independentAt_rightOrder {R : Finset E} (S : TripleOrder R)
    (base : ConfigSpace E) (z : E) :
    independentAt S.rightOrder base z = (tripleModeAt S base z).rightIndependent := by
  induction S with
  | done => rfl
  | @node R e he mode closed opened ihc iho =>
      simp only [TripleOrder.rightOrder, independentAt, tripleModeAt]
      by_cases hze : z = e
      · simp [hze]
      · simp only [hze, if_false]
        split <;> assumption

lemma causalMixLabels_leftOrder_apply
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) (i : Fin (Fintype.card E)) :
    causalMixLabels S.leftOrder base U V i =
      match tripleModeAt S base (realizedEquiv S.leftOrder base i) with
      | .before => V i
      | .flip => U i
      | .after => U i := by
  unfold causalMixLabels
  rw [independentAt_leftOrder]
  cases tripleModeAt S base (realizedEquiv S.leftOrder base i) <;> rfl

lemma causalMixLabels_rightOrder_apply
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) (i : Fin (Fintype.card E)) :
    causalMixLabels S.rightOrder base U V i =
      match tripleModeAt S base (realizedEquiv S.rightOrder base i) with
      | .before => V i
      | .flip => V i
      | .after => U i := by
  unfold causalMixLabels
  rw [independentAt_rightOrder]
  cases tripleModeAt S base (realizedEquiv S.rightOrder base i) <;> rfl


lemma causalMixLabels_left_eq_right_of_mode_ne_flip
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U V : Fin (Fintype.card E) → ℝ) (i : Fin (Fintype.card E))
    (hmode : tripleModeAt S base (realizedEquiv S.leftOrder base i) ≠ .flip) :
    causalMixLabels S.leftOrder base U V i =
      causalMixLabels S.rightOrder base U V i := by
  rw [causalMixLabels_leftOrder_apply, causalMixLabels_rightOrder_apply]
  rw [← realizedEquiv_leftOrder_eq_rightOrder S base]
  cases hm : tripleModeAt S base (realizedEquiv S.leftOrder base i) <;>
    simp_all


lemma causalMixLabels_leftOrder_eq_rightOrder_of_no_flip
    (S : TripleOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (hno : ∀ e, tripleModeAt S base e ≠ .flip)
    (U V : Fin (Fintype.card E) → ℝ) :
    causalMixLabels S.leftOrder base U V =
      causalMixLabels S.rightOrder base U V := by
  funext i
  exact causalMixLabels_left_eq_right_of_mode_ne_flip S base U V i
    (hno (realizedEquiv S.leftOrder base i))

lemma measurable_causalMixLabels_right
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U : Fin (Fintype.card E) → ℝ) :
    Measurable (fun V => causalMixLabels S base U V) := by
  apply measurable_pi_lambda
  intro i
  unfold causalMixLabels
  by_cases h : independentAt S base (realizedEquiv S base i)
  · simpa [h] using
      (measurable_pi_apply i : Measurable (fun V : Fin (Fintype.card E) → ℝ => V i))
  · simpa [h] using
      (measurable_const : Measurable (fun _ : Fin (Fintype.card E) → ℝ => U i))


lemma measurable_causalMixLabels_prod
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E) :
    Measurable (fun p : (Fin (Fintype.card E) → ℝ) ×
        (Fin (Fintype.card E) → ℝ) => causalMixLabels S base p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  unfold causalMixLabels
  by_cases h : independentAt S base (realizedEquiv S base i)
  · simp only [h, if_true]
    exact (measurable_pi_apply i).comp measurable_snd
  · simp only [h, if_false]
    exact (measurable_pi_apply i).comp measurable_fst


lemma causalMixLabels_mono_right
    (S : CausalOrder (Finset.univ : Finset E)) (base : ConfigSpace E)
    (U : Fin (Fintype.card E) → ℝ) :
    Monotone (fun V => causalMixLabels S base U V) := by
  intro V V' hVV i
  change (if independentAt S base (realizedEquiv S base i) then V i else U i) ≤
    (if independentAt S base (realizedEquiv S base i) then V' i else U i)
  by_cases h : independentAt S base (realizedEquiv S base i)
  · simpa [h] using hVV i
  · simp [h]


end AdaptiveCausalKernel
end OSSS
end StatMech
