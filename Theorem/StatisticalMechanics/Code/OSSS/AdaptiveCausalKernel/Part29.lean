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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part29
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


lemma baseSum_split (F : Finset E) (seed : ConfigSpace E)
    (H : ConfigSpace E → ℝ) (e : E) (he : e ∉ F) :
    baseSum F seed H =
      baseSum (insert e F) (Function.update seed e false) H +
        baseSum (insert e F) (Function.update seed e true) H := by
  unfold baseSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro base _
  by_cases hA : Agree F seed base
  · by_cases hb : base e
    · have hfalse : ¬ Agree (insert e F) (Function.update seed e false) base := by
        intro h
        have := h e (Finset.mem_insert_self e F)
        simp [hb] at this
      have htrue : Agree (insert e F) (Function.update seed e true) base := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · simp [hb]
        · have hze : z ≠ e := fun h => he (h ▸ hz)
          rw [Function.update_of_ne hze]
          exact hA z hz
      simp [hA, hfalse, htrue]
    · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
      have hfalse : Agree (insert e F) (Function.update seed e false) base := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · simp [hb']
        · have hze : z ≠ e := fun h => he (h ▸ hz)
          rw [Function.update_of_ne hze]
          exact hA z hz
      have htrue : ¬ Agree (insert e F) (Function.update seed e true) base := by
        intro h
        have := h e (Finset.mem_insert_self e F)
        simp [hb'] at this
      simp [hA, hfalse, htrue]
  · have hchild : ∀ b : Bool,
        ¬ Agree (insert e F) (Function.update seed e b) base := by
      intro b h
      apply hA
      intro z hz
      have hze : z ≠ e := fun hze => he (hze ▸ hz)
      have hz' := h z (Finset.mem_insert_of_mem hz)
      rw [Function.update_of_ne hze] at hz'
      exact hz'
    simp [hA, hchild]

lemma baseSum_condMass_self_eq_one (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (seed : ConfigSpace E) :
    baseSum F seed (fun base => condMass μ F base base) = 1 := by
  have heq : baseSum F seed (fun base => condMass μ F base base) =
      ∑ base, condMass μ F seed base := by
    unfold baseSum
    apply Finset.sum_congr rfl
    intro base _
    by_cases hA : Agree F seed base
    · rw [if_pos hA]
      unfold condMass
      change ((if Agree F base base then μ base else 0) / condNorm μ F base) =
        (if Agree F seed base then μ base else 0) / condNorm μ F seed
      rw [if_pos (agree_self F base), if_pos hA]
      rw [condNorm_congr μ F seed base (fun e he => (hA e he).symm)]
    · rw [if_neg hA]
      unfold condMass
      change 0 = (if Agree F seed base then μ base else 0) / condNorm μ F seed
      rw [if_neg hA]
      simp
  rw [heq, condMass_sum F seed (condNorm_pos hpos F seed).ne']

theorem baseSum_tripleJointProb_eq_tripleProb (μ : ConfigSpace E → ℝ)
    (F : Finset E) (seed left right : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base => tripleJointProb μ F base left right S) =
      tripleProb μ F seed left right S := by
  induction S generalizing F seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum tripleJointProb tripleProb
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro base _ hne
        have hnA : ¬ Agree Finset.univ seed base := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [tripleProb]
      rw [baseSum_split F seed (fun base =>
        tripleJointProb μ F base left right (.node e he mode closed opened)) e heF]
      have hbranch (b : Bool) :
          baseSum (insert e F) (Function.update seed e b)
              (fun base => tripleJointProb μ F base left right
                (.node e he mode closed opened)) =
            tripleWeight mode (condProbClosed μ F seed e)
                (condProbClosed μ F left e) (condProbClosed μ F right e)
                b (left e) (right e) *
              baseSum (insert e F) (Function.update seed e b)
                (fun base => tripleJointProb μ (insert e F) base left right
                  (if b then opened else closed)) := by
        unfold baseSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro base _
        by_cases hA : Agree (insert e F) (Function.update seed e b) base
        · have hbit : base e = b := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed base := by
            intro z hz
            have hze : z ≠ e := fun hze => heF (hze ▸ hz)
            have h := hA z (Finset.mem_insert_of_mem hz)
            rw [Function.update_of_ne hze] at h
            exact h
          have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
            condProbClosed_congr μ F base seed e (fun z hz => hag z hz)
          simp only [hA, if_true]
          rw [tripleJointProb, hbit, hq]
          cases b <;> rfl
        · simp [hA]
      rw [hbranch false, hbranch true]
      simp only [Bool.false_eq_true, if_false, if_true]
      rw [ihc (insert e F) (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update seed e true) hchild]


theorem baseSum_flip_tripleJointProb_eq_flipTripleProb
    (μ : ConfigSpace E → ℝ) (F : Finset E)
    (seed left right : ConfigSpace E) (z : E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base =>
      (if tripleModeAt S base z = .flip then 1 else 0) *
        tripleJointProb μ F base left right S) =
      flipTripleProb μ F seed left right z S := by
  induction S generalizing F seed with
  | done => simp [baseSum, tripleModeAt, flipTripleProb]
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      by_cases hze : z = e
      · subst z
        by_cases hm : mode = .flip
        · subst mode
          simp only [tripleModeAt, if_pos rfl, if_true, one_mul]
          rw [baseSum_tripleJointProb_eq_tripleProb μ F seed left right
            (.node e he .flip closed opened) hR]
          simp [flipTripleProb]
        · have hm' : mode ≠ TripleMode.flip := hm
          simp only [tripleModeAt, if_pos rfl, hm', if_false, zero_mul]
          simp [baseSum, flipTripleProb, hm']
      · rw [baseSum_split F seed (fun base =>
          (if tripleModeAt (.node e he mode closed opened) base z = .flip
            then 1 else 0) *
            tripleJointProb μ F base left right
              (.node e he mode closed opened)) e heF]
        have hbranch (b : Bool) :
            baseSum (insert e F) (Function.update seed e b)
                (fun base =>
                  (if tripleModeAt (.node e he mode closed opened) base z = .flip
                    then 1 else 0) *
                    tripleJointProb μ F base left right
                      (.node e he mode closed opened)) =
              tripleWeight mode (condProbClosed μ F seed e)
                  (condProbClosed μ F left e) (condProbClosed μ F right e)
                  b (left e) (right e) *
                baseSum (insert e F) (Function.update seed e b)
                  (fun base =>
                    (if tripleModeAt (if b then opened else closed) base z = .flip
                      then 1 else 0) *
                      tripleJointProb μ (insert e F) base left right
                        (if b then opened else closed)) := by
          unfold baseSum
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro base _
          by_cases hA : Agree (insert e F) (Function.update seed e b) base
          · have hbit : base e = b := by
              have h := hA e (Finset.mem_insert_self e F)
              simpa using h
            have hag : Agree F seed base := by
              intro x hx
              have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
              have h := hA x (Finset.mem_insert_of_mem hx)
              rw [Function.update_of_ne hxe] at h
              exact h
            have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
              condProbClosed_congr μ F base seed e (fun x hx => hag x hx)
            simp only [hA, if_true]
            rw [tripleJointProb, hbit, hq]
            cases b
            · by_cases hm : tripleModeAt closed base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, mul_assoc]
            · by_cases hm : tripleModeAt opened base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, mul_assoc]
          · simp [hA]
        rw [hbranch false, hbranch true]
        simp only [Bool.false_eq_true, if_false, if_true]
        rw [ihc (insert e F) (Function.update seed e false) hchild]
        rw [iho (insert e F) (Function.update seed e true) hchild]
        simp [flipTripleProb, hze]

theorem baseSum_crossTripleJointProb_eq_crossTripleProb (μ : ConfigSpace E → ℝ)
    (F : Finset E) (seed left right : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base => crossTripleJointProb μ F base left right S) =
      crossTripleProb μ F seed left right S := by
  induction S generalizing F seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum crossTripleJointProb crossTripleProb
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro base _ hne
        have hnA : ¬ Agree Finset.univ seed base := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [crossTripleProb]
      rw [baseSum_split F seed (fun base =>
        crossTripleJointProb μ F base left right (.node e he mode closed opened)) e heF]
      have hbranch (b : Bool) :
          baseSum (insert e F) (Function.update seed e b)
              (fun base => crossTripleJointProb μ F base left right
                (.node e he mode closed opened)) =
            crossTripleWeight mode (condProbClosed μ F seed e)
                (condProbClosed μ F left e) (condProbClosed μ F right e)
                b (left e) (right e) *
              baseSum (insert e F) (Function.update seed e b)
                (fun base => crossTripleJointProb μ (insert e F) base left right
                  (if b then opened else closed)) := by
        unfold baseSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro base _
        by_cases hA : Agree (insert e F) (Function.update seed e b) base
        · have hbit : base e = b := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed base := by
            intro z hz
            have hze : z ≠ e := fun hze => heF (hze ▸ hz)
            have h := hA z (Finset.mem_insert_of_mem hz)
            rw [Function.update_of_ne hze] at h
            exact h
          have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
            condProbClosed_congr μ F base seed e (fun z hz => hag z hz)
          simp only [hA, if_true]
          rw [crossTripleJointProb, hbit, hq]
          cases b <;> rfl
        · simp [hA]
      rw [hbranch false, hbranch true]
      simp only [Bool.false_eq_true, if_false, if_true]
      rw [ihc (insert e F) (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update seed e true) hchild]


theorem baseSum_flip_crossTripleJointProb_eq_flipCrossTripleProb
    (μ : ConfigSpace E → ℝ) (F : Finset E)
    (seed left right : ConfigSpace E) (z : E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base =>
      (if tripleModeAt S base z = .flip then 1 else 0) *
        crossTripleJointProb μ F base left right S) =
      flipCrossTripleProb μ F seed left right z S := by
  induction S generalizing F seed with
  | done => simp [baseSum, tripleModeAt, flipCrossTripleProb]
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      by_cases hze : z = e
      · subst z
        by_cases hm : mode = .flip
        · subst mode
          simp only [tripleModeAt, if_pos rfl, if_true, one_mul]
          rw [baseSum_crossTripleJointProb_eq_crossTripleProb μ F seed left right
            (.node e he .flip closed opened) hR]
          simp [flipCrossTripleProb]
        · have hm' : mode ≠ TripleMode.flip := hm
          simp only [tripleModeAt, if_pos rfl, hm', if_false, zero_mul]
          simp [baseSum, flipCrossTripleProb, hm']
      · rw [baseSum_split F seed (fun base =>
          (if tripleModeAt (.node e he mode closed opened) base z = .flip
            then 1 else 0) *
            crossTripleJointProb μ F base left right
              (.node e he mode closed opened)) e heF]
        have hbranch (b : Bool) :
            baseSum (insert e F) (Function.update seed e b)
                (fun base =>
                  (if tripleModeAt (.node e he mode closed opened) base z = .flip
                    then 1 else 0) *
                    crossTripleJointProb μ F base left right
                      (.node e he mode closed opened)) =
              crossTripleWeight mode (condProbClosed μ F seed e)
                  (condProbClosed μ F left e) (condProbClosed μ F right e)
                  b (left e) (right e) *
                baseSum (insert e F) (Function.update seed e b)
                  (fun base =>
                    (if tripleModeAt (if b then opened else closed) base z = .flip
                      then 1 else 0) *
                      crossTripleJointProb μ (insert e F) base left right
                        (if b then opened else closed)) := by
          unfold baseSum
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro base _
          by_cases hA : Agree (insert e F) (Function.update seed e b) base
          · have hbit : base e = b := by
              have h := hA e (Finset.mem_insert_self e F)
              simpa using h
            have hag : Agree F seed base := by
              intro x hx
              have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
              have h := hA x (Finset.mem_insert_of_mem hx)
              rw [Function.update_of_ne hxe] at h
              exact h
            have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
              condProbClosed_congr μ F base seed e (fun x hx => hag x hx)
            simp only [hA, if_true]
            rw [crossTripleJointProb, hbit, hq]
            cases b
            · by_cases hm : tripleModeAt closed base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, mul_assoc]
            · by_cases hm : tripleModeAt opened base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, mul_assoc]
          · simp [hA]
        rw [hbranch false, hbranch true]
        simp only [Bool.false_eq_true, if_false, if_true]
        rw [ihc (insert e F) (Function.update seed e false) hchild]
        rw [iho (insert e F) (Function.update seed e true) hchild]
        simp [flipCrossTripleProb, hze]

theorem sum_tripleJointProb_empty_eq_tripleProb (μ : ConfigSpace E → ℝ)
    (seed left right : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ base, tripleJointProb μ ∅ base left right S =
      tripleProb μ ∅ seed left right S := by
  have h := baseSum_tripleJointProb_eq_tripleProb μ ∅ seed left right S (by simp)
  simpa [baseSum, Agree] using h

theorem sum_pairedCube_frozenTripleCodeAtom_eq_tripleProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (seed left right : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ base, (pairedCube (Fintype.card E)
        (frozenTripleCodeAtom μ S base left right)).toReal =
      tripleProb μ ∅ seed left right S := by
  simp_rw [pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb μ hpos]
  exact sum_tripleJointProb_empty_eq_tripleProb μ seed left right S


theorem sum_crossTripleJointProb_empty_eq_crossTripleProb (μ : ConfigSpace E → ℝ)
    (seed left right : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ base, crossTripleJointProb μ ∅ base left right S =
      crossTripleProb μ ∅ seed left right S := by
  have h := baseSum_crossTripleJointProb_eq_crossTripleProb
    μ ∅ seed left right S (by simp)
  simpa [baseSum, Agree] using h

theorem sum_tripleCube_frozenCrossCodeAtom_eq_crossTripleProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (seed left right : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ base, (tripleCube (Fintype.card E)
        (frozenCrossCodeAtom μ S base left right)).toReal =
      crossTripleProb μ ∅ seed left right S := by
  simp_rw [tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb μ hpos]
  exact sum_crossTripleJointProb_empty_eq_crossTripleProb μ seed left right S


theorem sum_frozenTripleCodeAtom_observable_eq_tripleProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (seed : ConfigSpace E) (S : TripleOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    ∑ base, ∑ left, ∑ right, g left right *
        (pairedCube (Fintype.card E)
          (frozenTripleCodeAtom μ S base left right)).toReal =
      ∑ left, ∑ right, g left right * tripleProb μ ∅ seed left right S := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  rw [← Finset.mul_sum]
  rw [sum_pairedCube_frozenTripleCodeAtom_eq_tripleProb μ hpos seed left right S]


theorem sum_frozenCrossCodeAtom_observable_eq_crossTripleProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (seed : ConfigSpace E) (S : TripleOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ConfigSpace E → ℝ) :
    ∑ base, ∑ left, ∑ right, g left right *
        (tripleCube (Fintype.card E)
          (frozenCrossCodeAtom μ S base left right)).toReal =
      ∑ left, ∑ right, g left right * crossTripleProb μ ∅ seed left right S := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  rw [← Finset.mul_sum]
  rw [sum_tripleCube_frozenCrossCodeAtom_eq_crossTripleProb μ hpos seed left right S]


theorem sum_frozenTripleCodeAtom_weighted_eq_tripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ConfigSpace E → ConfigSpace E → ℝ) :
    ∑ base, ∑ left, ∑ right, g base left right *
        (pairedCube (Fintype.card E)
          (frozenTripleCodeAtom μ S base left right)).toReal =
      ∑ base, ∑ left, ∑ right, g base left right *
        tripleJointProb μ ∅ base left right S := by
  simp_rw [pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb μ hpos]


theorem sum_frozenCrossCodeAtom_weighted_eq_crossTripleJointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (S : TripleOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ConfigSpace E → ConfigSpace E → ℝ) :
    ∑ base, ∑ left, ∑ right, g base left right *
        (tripleCube (Fintype.card E)
          (frozenCrossCodeAtom μ S base left right)).toReal =
      ∑ base, ∑ left, ∑ right, g base left right *
        crossTripleJointProb μ ∅ base left right S := by
  simp_rw [tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb μ hpos]

theorem baseSum_jointProb_eq_targetProb (μ : ConfigSpace E → ℝ)
    (F : Finset E) (seed target : ConfigSpace E) {R : Finset E}
    (S : CausalOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base => jointProb μ F base target S) =
      targetProb μ F seed target S := by
  induction S generalizing F seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum jointProb targetProb
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro base _ hne
        have hnA : ¬ Agree Finset.univ seed base := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he independent closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [targetProb]
      rw [baseSum_split F seed (fun base => jointProb μ F base target
        (.node e he independent closed opened)) e heF]
      have hbranch (b : Bool) :
          baseSum (insert e F) (Function.update seed e b)
              (fun base => jointProb μ F base target
                (.node e he independent closed opened)) =
            splitWeight independent (condProbClosed μ F seed e)
                (condProbClosed μ F target e) b (target e) *
              baseSum (insert e F) (Function.update seed e b)
                (fun base => jointProb μ (insert e F) base target
                  (if b then opened else closed)) := by
        unfold baseSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro base _
        by_cases hA : Agree (insert e F) (Function.update seed e b) base
        · have hbit : base e = b := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed base := by
            intro z hz
            have hze : z ≠ e := fun hze => heF (hze ▸ hz)
            have h := hA z (Finset.mem_insert_of_mem hz)
            rw [Function.update_of_ne hze] at h
            exact h
          have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
            condProbClosed_congr μ F base seed e (fun z hz => hag z hz)
          simp only [hA, if_true]
          rw [jointProb, hbit, hq]
          cases b <;> rfl
        · simp [hA]
      rw [hbranch false, hbranch true]
      simp only [Bool.false_eq_true, if_false, if_true]
      rw [ihc (insert e F) (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update seed e true) hchild]

theorem sum_jointProb_empty_eq_targetProb (μ : ConfigSpace E → ℝ)
    (seed target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    ∑ base, jointProb μ ∅ base target S = targetProb μ ∅ seed target S := by
  have h := baseSum_jointProb_eq_targetProb μ ∅ seed target S (by simp)
  simpa [baseSum, Agree] using h

theorem baseSum_tripleJointProb_right_eq_jointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (base left seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun right => tripleJointProb μ F base left right S) =
      jointProb μ F base left S.leftOrder := by
  induction S generalizing F seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum tripleJointProb jointProb TripleOrder.leftOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro right _ hne
        have hnA : ¬ Agree Finset.univ seed right := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F seed e
      rw [baseSum_split F seed (fun right => tripleJointProb μ F base left right
        (.node e he mode closed opened)) e heF]
      have hbranch (z : Bool) :
          baseSum (insert e F) (Function.update seed e z)
              (fun right => tripleJointProb μ F base left right
                (.node e he mode closed opened)) =
            tripleWeight mode a q r (base e) (left e) z *
              baseSum (insert e F) (Function.update seed e z)
                (fun right => tripleJointProb μ (insert e F) base left right
                  (if base e then opened else closed)) := by
        unfold baseSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro right _
        by_cases hA : Agree (insert e F) (Function.update seed e z) right
        · have hbit : right e = z := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed right := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hr : condProbClosed μ F right e = r := by
            change condProbClosed μ F right e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F right seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [tripleJointProb, hr, hbit]
          cases hb : base e <;> rfl
        · simp [hA]
      rw [hbranch false, hbranch true]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd left
      have hr := hbnd seed
      by_cases hb : base e
      · simp only [hb, if_true]
        rw [iho (insert e F) (Function.update seed e false) hchild]
        rw [iho (insert e F) (Function.update seed e true) hchild]
        simp only [TripleOrder.leftOrder, jointProb, hb, if_true]
        rw [← add_mul]
        rw [tripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
          true (left e)]
      · simp only [hb, Bool.false_eq_true, if_false]
        rw [ihc (insert e F) (Function.update seed e false) hchild]
        rw [ihc (insert e F) (Function.update seed e true) hchild]
        simp only [TripleOrder.leftOrder, jointProb, hb, Bool.false_eq_true, if_false]
        rw [← add_mul]
        rw [tripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
          false (left e)]

theorem baseSum_tripleJointProb_left_eq_jointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (base right seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun left => tripleJointProb μ F base left right S) =
      jointProb μ F base right S.rightOrder := by
  induction S generalizing F seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum tripleJointProb jointProb TripleOrder.rightOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro left _ hne
        have hnA : ¬ Agree Finset.univ seed left := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F seed e
      let r := condProbClosed μ F right e
      rw [baseSum_split F seed (fun left => tripleJointProb μ F base left right
        (.node e he mode closed opened)) e heF]
      have hbranch (y : Bool) :
          baseSum (insert e F) (Function.update seed e y)
              (fun left => tripleJointProb μ F base left right
                (.node e he mode closed opened)) =
            tripleWeight mode a q r (base e) y (right e) *
              baseSum (insert e F) (Function.update seed e y)
                (fun left => tripleJointProb μ (insert e F) base left right
                  (if base e then opened else closed)) := by
        unfold baseSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro left _
        by_cases hA : Agree (insert e F) (Function.update seed e y) left
        · have hbit : left e = y := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed left := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hq : condProbClosed μ F left e = q := by
            change condProbClosed μ F left e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F left seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [tripleJointProb, hq, hbit]
          cases hb : base e <;> rfl
        · simp [hA]
      rw [hbranch false, hbranch true]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd seed
      have hr := hbnd right
      by_cases hb : base e
      · simp only [hb, if_true]
        rw [iho (insert e F) (Function.update seed e false) hchild]
        rw [iho (insert e F) (Function.update seed e true) hchild]
        simp only [TripleOrder.rightOrder, jointProb, hb, if_true]
        rw [← add_mul]
        rw [tripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
          true (right e)]
      · simp only [hb, Bool.false_eq_true, if_false]
        rw [ihc (insert e F) (Function.update seed e false) hchild]
        rw [ihc (insert e F) (Function.update seed e true) hchild]
        simp only [TripleOrder.rightOrder, jointProb, hb, Bool.false_eq_true, if_false]
        rw [← add_mul]
        rw [tripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
          false (right e)]

theorem sum_tripleJointProb_right_eq_jointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (base left seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ right, tripleJointProb μ ∅ base left right S =
      jointProb μ ∅ base left S.leftOrder := by
  have h := baseSum_tripleJointProb_right_eq_jointProb
    μ hpos ∅ base left seed S (by simp)
  simpa [baseSum, Agree] using h

theorem sum_tripleJointProb_left_eq_jointProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (base right seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ left, tripleJointProb μ ∅ base left right S =
      jointProb μ ∅ base right S.rightOrder := by
  have h := baseSum_tripleJointProb_left_eq_jointProb
    μ hpos ∅ base right seed S (by simp)
  simpa [baseSum, Agree] using h

theorem baseSum_tripleProb_right_eq_targetProb (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (base left seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun right => tripleProb μ F base left right S) =
      targetProb μ F base left S.leftOrder := by
  induction S generalizing F base seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum tripleProb targetProb TripleOrder.leftOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro right _ hne
        have hnA : ¬ Agree Finset.univ seed right := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [TripleOrder.leftOrder, targetProb]
      rw [baseSum_split F seed (fun right => tripleProb μ F base left right
        (.node e he mode closed opened)) e heF]
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F seed e
      have hbranch (z : Bool) :
          baseSum (insert e F) (Function.update seed e z)
              (fun right => tripleProb μ F base left right
                (.node e he mode closed opened)) =
            tripleWeight mode a q r false (left e) z *
                baseSum (insert e F) (Function.update seed e z)
                  (fun right => tripleProb μ (insert e F)
                    (Function.update base e false) left right closed) +
              tripleWeight mode a q r true (left e) z *
                baseSum (insert e F) (Function.update seed e z)
                  (fun right => tripleProb μ (insert e F)
                    (Function.update base e true) left right opened) := by
        unfold baseSum
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro right _
        by_cases hA : Agree (insert e F) (Function.update seed e z) right
        · have hbit : right e = z := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed right := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hr : condProbClosed μ F right e = r := by
            change condProbClosed μ F right e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F right seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [tripleProb, hr, hbit]
        · simp [hA]
      rw [hbranch false, hbranch true]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e false) hchild]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e true) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e true) hchild]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd left
      have hr := hbnd seed
      let C := targetProb μ (insert e F) (Function.update base e false) left
        closed.leftOrder
      let D := targetProb μ (insert e F) (Function.update base e true) left
        opened.leftOrder
      change
        (tripleWeight mode a q r false (left e) false * C +
            tripleWeight mode a q r true (left e) false * D) +
          (tripleWeight mode a q r false (left e) true * C +
            tripleWeight mode a q r true (left e) true * D) =
        splitWeight mode.leftIndependent a q false (left e) * C +
          splitWeight mode.leftIndependent a q true (left e) * D
      calc
        _ = (tripleWeight mode a q r false (left e) false +
              tripleWeight mode a q r false (left e) true) * C +
            (tripleWeight mode a q r true (left e) false +
              tripleWeight mode a q r true (left e) true) * D := by ring
        _ = _ := by
          rw [tripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            false (left e)]
          rw [tripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            true (left e)]

theorem baseSum_tripleProb_left_eq_targetProb (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (base right seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun left => tripleProb μ F base left right S) =
      targetProb μ F base right S.rightOrder := by
  induction S generalizing F base seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum tripleProb targetProb TripleOrder.rightOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro left _ hne
        have hnA : ¬ Agree Finset.univ seed left := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [TripleOrder.rightOrder]
      rw [targetProb]
      rw [baseSum_split F seed (fun left => tripleProb μ F base left right
        (.node e he mode closed opened)) e heF]
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F seed e
      let r := condProbClosed μ F right e
      have hbranch (y : Bool) :
          baseSum (insert e F) (Function.update seed e y)
              (fun left => tripleProb μ F base left right
                (.node e he mode closed opened)) =
            tripleWeight mode a q r false y (right e) *
                baseSum (insert e F) (Function.update seed e y)
                  (fun left => tripleProb μ (insert e F)
                    (Function.update base e false) left right closed) +
              tripleWeight mode a q r true y (right e) *
                baseSum (insert e F) (Function.update seed e y)
                  (fun left => tripleProb μ (insert e F)
                    (Function.update base e true) left right opened) := by
        unfold baseSum
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro left _
        by_cases hA : Agree (insert e F) (Function.update seed e y) left
        · have hbit : left e = y := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed left := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hq : condProbClosed μ F left e = q := by
            change condProbClosed μ F left e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F left seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [tripleProb, hq, hbit]
        · simp [hA]
      rw [hbranch false, hbranch true]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e false) hchild]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e true) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e true) hchild]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd seed
      have hr := hbnd right
      let C := targetProb μ (insert e F) (Function.update base e false) right
        closed.rightOrder
      let D := targetProb μ (insert e F) (Function.update base e true) right
        opened.rightOrder
      change
        (tripleWeight mode a q r false false (right e) * C +
            tripleWeight mode a q r true false (right e) * D) +
          (tripleWeight mode a q r false true (right e) * C +
            tripleWeight mode a q r true true (right e) * D) =
        splitWeight mode.rightIndependent a r false (right e) * C +
          splitWeight mode.rightIndependent a r true (right e) * D
      calc
        _ = (tripleWeight mode a q r false false (right e) +
              tripleWeight mode a q r false true (right e)) * C +
            (tripleWeight mode a q r true false (right e) +
              tripleWeight mode a q r true true (right e)) * D := by ring
        _ = _ := by
          have h0 := tripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2
            hr.1 hr.2 false (right e)
          have h1 := tripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2
            hr.1 hr.2 true (right e)
          rw [h0, h1]

theorem baseSum_crossTripleProb_right_eq_targetProb (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (base left seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun right => crossTripleProb μ F base left right S) =
      targetProb μ F base left S.leftOrder := by
  induction S generalizing F base seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum crossTripleProb targetProb TripleOrder.leftOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro right _ hne
        have hnA : ¬ Agree Finset.univ seed right := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [TripleOrder.leftOrder, targetProb]
      rw [baseSum_split F seed (fun right => crossTripleProb μ F base left right
        (.node e he mode closed opened)) e heF]
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F left e
      let r := condProbClosed μ F seed e
      have hbranch (z : Bool) :
          baseSum (insert e F) (Function.update seed e z)
              (fun right => crossTripleProb μ F base left right
                (.node e he mode closed opened)) =
            crossTripleWeight mode a q r false (left e) z *
                baseSum (insert e F) (Function.update seed e z)
                  (fun right => crossTripleProb μ (insert e F)
                    (Function.update base e false) left right closed) +
              crossTripleWeight mode a q r true (left e) z *
                baseSum (insert e F) (Function.update seed e z)
                  (fun right => crossTripleProb μ (insert e F)
                    (Function.update base e true) left right opened) := by
        unfold baseSum
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro right _
        by_cases hA : Agree (insert e F) (Function.update seed e z) right
        · have hbit : right e = z := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed right := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hr : condProbClosed μ F right e = r := by
            change condProbClosed μ F right e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F right seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [crossTripleProb, hr, hbit]
        · simp [hA]
      rw [hbranch false, hbranch true]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e false) hchild]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e true) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e true) hchild]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd left
      have hr := hbnd seed
      let C := targetProb μ (insert e F) (Function.update base e false) left
        closed.leftOrder
      let D := targetProb μ (insert e F) (Function.update base e true) left
        opened.leftOrder
      change
        (crossTripleWeight mode a q r false (left e) false * C +
            crossTripleWeight mode a q r true (left e) false * D) +
          (crossTripleWeight mode a q r false (left e) true * C +
            crossTripleWeight mode a q r true (left e) true * D) =
        splitWeight mode.leftIndependent a q false (left e) * C +
          splitWeight mode.leftIndependent a q true (left e) * D
      calc
        _ = (crossTripleWeight mode a q r false (left e) false +
              crossTripleWeight mode a q r false (left e) true) * C +
            (crossTripleWeight mode a q r true (left e) false +
              crossTripleWeight mode a q r true (left e) true) * D := by ring
        _ = _ := by
          rw [crossTripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            false (left e)]
          rw [crossTripleWeight_sum_third mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            true (left e)]

theorem baseSum_crossTripleProb_left_eq_targetProb (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E)
    (base right seed : ConfigSpace E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun left => crossTripleProb μ F base left right S) =
      targetProb μ F base right S.rightOrder := by
  induction S generalizing F base seed with
  | done =>
      have hF : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold baseSum crossTripleProb targetProb TripleOrder.rightOrder
      rw [Finset.sum_eq_single seed]
      · simp [Agree]
      · intro left _ hne
        have hnA : ¬ Agree Finset.univ seed left := by
          intro hA
          apply hne
          funext z
          exact hA z (Finset.mem_univ z)
        simp [hnA]
      · simp
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [TripleOrder.rightOrder]
      rw [targetProb]
      rw [baseSum_split F seed (fun left => crossTripleProb μ F base left right
        (.node e he mode closed opened)) e heF]
      let a := condProbClosed μ F base e
      let q := condProbClosed μ F seed e
      let r := condProbClosed μ F right e
      have hbranch (y : Bool) :
          baseSum (insert e F) (Function.update seed e y)
              (fun left => crossTripleProb μ F base left right
                (.node e he mode closed opened)) =
            crossTripleWeight mode a q r false y (right e) *
                baseSum (insert e F) (Function.update seed e y)
                  (fun left => crossTripleProb μ (insert e F)
                    (Function.update base e false) left right closed) +
              crossTripleWeight mode a q r true y (right e) *
                baseSum (insert e F) (Function.update seed e y)
                  (fun left => crossTripleProb μ (insert e F)
                    (Function.update base e true) left right opened) := by
        unfold baseSum
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro left _
        by_cases hA : Agree (insert e F) (Function.update seed e y) left
        · have hbit : left e = y := by
            have h := hA e (Finset.mem_insert_self e F)
            simpa using h
          have hag : Agree F seed left := by
            intro x hx
            have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
            have h := hA x (Finset.mem_insert_of_mem hx)
            rw [Function.update_of_ne hxe] at h
            exact h
          have hq : condProbClosed μ F left e = q := by
            change condProbClosed μ F left e = condProbClosed μ F seed e
            exact condProbClosed_congr μ F left seed e (fun x hx => hag x hx)
          simp only [hA, if_true]
          rw [crossTripleProb, hq, hbit]
        · simp [hA]
      rw [hbranch false, hbranch true]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e false) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e false) hchild]
      rw [ihc (insert e F) (Function.update base e false)
        (Function.update seed e true) hchild]
      rw [iho (insert e F) (Function.update base e true)
        (Function.update seed e true) hchild]
      have hbnd (x : ConfigSpace E) :
          0 ≤ condProbClosed μ F x e ∧ condProbClosed μ F x e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x),
          condProbBit_le_one (fun ω => (hpos ω).le) F x e false
          (condNorm_pos hpos F x)⟩
      have ha := hbnd base
      have hq := hbnd seed
      have hr := hbnd right
      let C := targetProb μ (insert e F) (Function.update base e false) right
        closed.rightOrder
      let D := targetProb μ (insert e F) (Function.update base e true) right
        opened.rightOrder
      change
        (crossTripleWeight mode a q r false false (right e) * C +
            crossTripleWeight mode a q r true false (right e) * D) +
          (crossTripleWeight mode a q r false true (right e) * C +
            crossTripleWeight mode a q r true true (right e) * D) =
        splitWeight mode.rightIndependent a r false (right e) * C +
          splitWeight mode.rightIndependent a r true (right e) * D
      calc
        _ = (crossTripleWeight mode a q r false false (right e) +
              crossTripleWeight mode a q r false true (right e)) * C +
            (crossTripleWeight mode a q r true false (right e) +
              crossTripleWeight mode a q r true true (right e)) * D := by ring
        _ = _ := by
          rw [crossTripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            false (right e)]
          rw [crossTripleWeight_sum_second mode a q r ha.1 ha.2 hq.1 hq.2 hr.1 hr.2
            true (right e)]


theorem jointProb_zero_support (μ : ConfigSpace E → ℝ) (T : DecisionTree E)
    (F R : Finset E) (known base target : ConfigSpace E)
    (hR : R = Finset.univ \ F)
    (hknown : ∀ e, e ∉ R → known e = base e)
    (hagree : Agree F base target)
    (hnz : jointProb μ F base target (extendDecisionTreeAt 0 T known R) ≠ 0) :
    T.eval base = T.eval target := by
  induction T generalizing F R known with
  | leaf b => rfl
  | node e opened closed iho ihc =>
      rw [extendDecisionTreeAt] at hnz
      by_cases heR : e ∈ R
      · rw [dif_pos heR] at hnz
        have heF : e ∉ F := by
          intro heF
          have hmem : e ∈ Finset.univ \ F := by rw [← hR]; exact heR
          exact (Finset.mem_sdiff.mp hmem).2 heF
        have hthr : condProbClosed μ F base e = condProbClosed μ F target e :=
          condProbClosed_congr μ F base target e (fun z hz => (hagree z hz).symm)
        have hR' : R.erase e = Finset.univ \ insert e F := by
          rw [hR]
          ext z
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
            true_and, Finset.mem_insert]
          tauto
        by_cases hb : base e
        · simp only [hb, if_true, Nat.lt_irrefl, decide_false, jointProb,
            splitWeight, Bool.false_eq_true, if_false] at hnz
          have hbit : target e = true := by
            by_contra ht
            have ht' : target e = false := Bool.eq_false_of_not_eq_true ht
            rw [hthr, ht', overlapWeight_same_threshold_ne _ (by decide)] at hnz
            simp at hnz
          have htail : jointProb μ (insert e F) base target
              (extendDecisionTreeAt 0 opened (Function.update known e true) (R.erase e)) ≠ 0 :=
            (mul_ne_zero_iff.mp hnz).2
          have hk' : ∀ z, z ∉ R.erase e → Function.update known e true z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z; simp [hb]
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          have ha' : Agree (insert e F) base target := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · simpa [hb] using hbit.symm
            · exact hagree z hz
          simp only [DecisionTree.eval, hb, hbit, if_true]
          exact iho (insert e F) (R.erase e) (Function.update known e true)
            hR' hk' ha' htail
        · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
          simp only [hb, Bool.false_eq_true, if_false, Nat.lt_irrefl, decide_false,
            jointProb, splitWeight] at hnz
          have hbit : target e = false := by
            by_contra ht
            have ht' : target e = true := Bool.eq_true_of_not_eq_false ht
            rw [hthr, ht', overlapWeight_same_threshold_ne _ (by decide)] at hnz
            simp at hnz
          have htail : jointProb μ (insert e F) base target
              (extendDecisionTreeAt 0 closed (Function.update known e false) (R.erase e)) ≠ 0 :=
            (mul_ne_zero_iff.mp hnz).2
          have hk' : ∀ z, z ∉ R.erase e → Function.update known e false z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z; simp [hb']
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          have ha' : Agree (insert e F) base target := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · simpa [hb'] using hbit.symm
            · exact hagree z hz
          simp only [DecisionTree.eval, hb, hbit, Bool.false_eq_true, if_false]
          exact ihc (insert e F) (R.erase e) (Function.update known e false)
            hR' hk' ha' htail
      · rw [dif_neg heR] at hnz
        have heF : e ∈ F := by
          by_contra heF
          have hmem : e ∈ Finset.univ \ F :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, heF⟩
          rw [← hR] at hmem
          exact heR hmem
        have hkb : known e = base e := hknown e heR
        have htb : target e = base e := hagree e heF
        by_cases hb : base e
        · simp only [hkb, hb, if_true] at hnz
          simp only [DecisionTree.eval, hb, htb, if_true]
          exact iho F R known hR hknown hagree hnz
        · simp only [hkb, hb, Bool.false_eq_true, if_false] at hnz
          simp only [DecisionTree.eval, hb, htb, Bool.false_eq_true, if_false]
          exact ihc F R known hR hknown hagree hnz

theorem jointProb_zero_support_univ (μ : ConfigSpace E → ℝ) (T : DecisionTree E)
    (base target : ConfigSpace E)
    (hnz : jointProb μ ∅ base target
      (extendDecisionTreeAt 0 T base (Finset.univ : Finset E)) ≠ 0) :
    T.eval base = T.eval target :=
  jointProb_zero_support μ T ∅ Finset.univ base base target
    (by simp) (by simp) (by simp [Agree]) hnz


end AdaptiveCausalKernel
end OSSS
end StatMech
