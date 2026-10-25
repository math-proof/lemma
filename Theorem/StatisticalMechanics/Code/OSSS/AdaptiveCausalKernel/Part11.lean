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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part11
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


theorem extendDecisionTreeTriple_none_leftOrder (T : DecisionTree E)
    (known : ConfigSpace E) (R : Finset E) :
    (extendDecisionTreeTriple none T known R).leftOrder =
      extendDecisionTreeAt 0 T known R := by
  induction T generalizing known R with
  | leaf b => simp [extendDecisionTreeTriple, extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple, extendDecisionTreeAt]
      by_cases he : e ∈ R
      · simp [he, TripleOrder.leftOrder, TripleMode.leftIndependent, ihc, iho]
      · simp [he]
        split <;> simp_all

theorem extendDecisionTreeTriple_none_rightOrder (T : DecisionTree E)
    (known : ConfigSpace E) (R : Finset E) :
    (extendDecisionTreeTriple none T known R).rightOrder =
      extendDecisionTreeAt 0 T known R := by
  induction T generalizing known R with
  | leaf b => simp [extendDecisionTreeTriple, extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple, extendDecisionTreeAt]
      by_cases he : e ∈ R
      · simp [he, TripleOrder.rightOrder, TripleMode.rightIndependent, ihc, iho]
      · simp [he]
        split <;> simp_all

lemma card_insert_inter_sub_one (P R : Finset E) (q : E) (hq : q ∈ R) :
    (insert q P ∩ R).card - 1 = (P ∩ R.erase q).card := by
  have hset : insert q P ∩ R = insert q (P ∩ R.erase q) := by
    ext z
    by_cases hzq : z = q
    · subst z
      simp [hq]
    · simp [hzq]
  rw [hset, Finset.card_insert_of_notMem]
  · simp
  · simp


theorem tripleModeAt_extendDecisionTreeTriple_eq_flip_of_fresh
    (T : DecisionTree E) (base known : ConfigSpace E) (R : Finset E)
    (hknown : ∀ z, z ∉ R → known z = base z) (t : ℕ) (e : E)
    (hq : PredictableTreeQuery.pathQuery T base t = some e)
    (hfresh : e ∉ LindebergTree.pathPrefix T base t) (heR : e ∈ R) :
    tripleModeAt
        (extendDecisionTreeTriple
          (some ((LindebergTree.pathPrefix T base t ∩ R).card)) T known R)
        base e = .flip := by
  induction T generalizing known R t with
  | leaf b => simp [PredictableTreeQuery.pathQuery] at hq
  | node q opened closed iho ihc =>
      cases t with
      | zero =>
          simp only [PredictableTreeQuery.pathQuery, Option.some.injEq] at hq
          subst e
          simp only [LindebergTree.pathPrefix_zero, Finset.empty_inter, Finset.card_empty]
          simp [extendDecisionTreeTriple, heR, tripleModeAt]
      | succ t =>
          let B := if base q then opened else closed
          have hqB : PredictableTreeQuery.pathQuery B base t = some e := by
            simpa [B, PredictableTreeQuery.pathQuery] using hq
          have hprefix : LindebergTree.pathPrefix (.node q opened closed) base (t + 1) =
              insert q (LindebergTree.pathPrefix B base t) := by
            simp [LindebergTree.pathPrefix_node_succ, B]
          have hefreshB : e ∉ LindebergTree.pathPrefix B base t := by
            intro he
            apply hfresh
            rw [hprefix]
            exact Finset.mem_insert_of_mem he
          have heq : e ≠ q := by
            intro he
            subst e
            apply hfresh
            rw [hprefix]
            exact Finset.mem_insert_self _ _
          by_cases hqR : q ∈ R
          · let P := LindebergTree.pathPrefix B base t
            let k := (P ∩ R.erase q).card
            have hphase : (insert q P ∩ R).card = k + 1 := by
              have hsub := card_insert_inter_sub_one P R q hqR
              have hpos : 0 < (insert q P ∩ R).card := by
                apply Finset.card_pos.mpr
                exact ⟨q, Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hqR⟩⟩
              dsimp only [k]
              omega
            have heErase : e ∈ R.erase q := Finset.mem_erase.mpr ⟨heq, heR⟩
            have hknown' (b : Bool) (hbq : b = base q) : ∀ z, z ∉ R.erase q →
                Function.update known q b z = base z := by
              intro z hz
              by_cases hzq : z = q
              · subst z
                simp [hbq]
              · rw [Function.update_of_ne hzq]
                apply hknown z
                intro hzR
                exact hz (Finset.mem_erase.mpr ⟨hzq, hzR⟩)
            rw [hprefix]
            change tripleModeAt
              (extendDecisionTreeTriple (some ((insert q P ∩ R).card))
                (.node q opened closed) known R) base e = .flip
            rw [hphase]
            simp only [extendDecisionTreeTriple, hqR, dif_pos, tripleModeAt, heq, if_false]
            by_cases hb : base q
            · simp only [hb, if_true]
              have hi := iho (Function.update known q true) (R.erase q)
                (hknown' true (by simp [hb])) t
                (by simpa [B, hb] using hqB)
                (by simpa [B, hb] using hefreshB) heErase
              simpa [k, P, B, hb] using hi
            · simp only [hb, Bool.false_eq_true, if_false]
              have hi := ihc (Function.update known q false) (R.erase q)
                (hknown' false (by simp [hb])) t
                (by simpa [B, hb] using hqB)
                (by simpa [B, hb] using hefreshB) heErase
              simpa [k, P, B, hb] using hi
          · have hphase :
                (insert q (LindebergTree.pathPrefix B base t) ∩ R).card =
                  (LindebergTree.pathPrefix B base t ∩ R).card := by
              congr 1
              ext z
              simp only [Finset.mem_inter, Finset.mem_insert]
              constructor
              · rintro ⟨rfl | hz, hzR⟩
                · exact False.elim (hqR hzR)
                · exact ⟨hz, hzR⟩
              · rintro ⟨hz, hzR⟩
                exact ⟨Or.inr hz, hzR⟩
            have hknownq : known q = base q := hknown q hqR
            rw [hprefix, hphase]
            rw [extendDecisionTreeTriple, dif_neg hqR]
            rw [hknownq]
            by_cases hb : base q
            · simp only [hb, if_true]
              simpa [B, hb] using iho known R hknown t
                (by simpa [B, hb] using hqB)
                (by simpa [B, hb] using hefreshB) heR
            · simp only [hb, Bool.false_eq_true, if_false]
              simpa [B, hb] using ihc known R hknown t
                (by simpa [B, hb] using hqB)
                (by simpa [B, hb] using hefreshB) heR

@[simp] theorem extendDecisionTreeTriple_leftOrder
    (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E) :
    (extendDecisionTreeTriple (some t) T known R).leftOrder =
      extendDecisionTreeAt t T known R := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeTriple, extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple, extendDecisionTreeAt]
      by_cases he : e ∈ R
      · simp only [he, dif_pos]
        cases t with
        | zero =>
            simp [TripleOrder.leftOrder, TripleMode.leftIndependent,
              extendDecisionTreeTriple_none_leftOrder]
        | succ t =>
            simp [TripleOrder.leftOrder, TripleMode.leftIndependent, ihc, iho]
      · by_cases hb : known e
        · simp [he, hb, iho]
        · simp [he, hb, ihc]

@[simp] theorem extendDecisionTreeTriple_rightOrder
    (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E) :
    (extendDecisionTreeTriple (some t) T known R).rightOrder =
      extendDecisionTreeAt (t + 1) T known R := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeTriple, extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple, extendDecisionTreeAt]
      by_cases he : e ∈ R
      · simp only [he, dif_pos]
        cases t with
        | zero =>
            simp [TripleOrder.rightOrder, TripleMode.rightIndependent,
              extendDecisionTreeTriple_none_rightOrder]
        | succ t =>
            simp [TripleOrder.rightOrder, TripleMode.rightIndependent, ihc, iho]
      · by_cases hb : known e
        · simp [he, hb, iho]
        · simp [he, hb, ihc]


theorem extendDecisionTreeTriple_known_congr (phase : Option ℕ)
    (T : DecisionTree E) (known known' : ConfigSpace E) (R : Finset E)
    (hknown : ∀ z, z ∉ R → known z = known' z) :
    extendDecisionTreeTriple phase T known R =
      extendDecisionTreeTriple phase T known' R := by
  induction T generalizing phase known known' R with
  | leaf b => rfl
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeTriple]
      by_cases he : e ∈ R
      · simp only [he, dif_pos]
        have hup (b : Bool) : ∀ z, z ∉ R.erase e →
            Function.update known e b z = Function.update known' e b z := by
          intro z hz
          by_cases hze : z = e
          · subst z
            simp
          · rw [Function.update_of_ne hze, Function.update_of_ne hze]
            apply hknown z
            intro hzR
            exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
        cases phase with
        | none =>
            simp only
            rw [ihc none _ _ _ (hup false), iho none _ _ _ (hup true)]
        | some t =>
            cases t with
            | zero =>
                simp only
                rw [ihc none _ _ _ (hup false), iho none _ _ _ (hup true)]
            | succ t =>
                simp only
                rw [ihc (some t) _ _ _ (hup false),
                  iho (some t) _ _ _ (hup true)]
      · simp only [he, dif_neg]
        have heq : known e = known' e := hknown e he
        by_cases hb : known e
        · have hb' : known' e := by simpa [heq] using hb
          simp only [hb, hb', if_true]
          exact iho phase known known' R hknown
        · have hb' : ¬ known' e := by simpa [heq] using hb
          simp only [hb, hb', Bool.false_eq_true, if_false]
          exact ihc phase known known' R hknown

@[simp] theorem extendDecisionTreeTriple_univ_seed_congr (phase : Option ℕ)
    (T : DecisionTree E) (known known' : ConfigSpace E) :
    extendDecisionTreeTriple phase T known (Finset.univ : Finset E) =
      extendDecisionTreeTriple phase T known' Finset.univ :=
  extendDecisionTreeTriple_known_congr phase T known known' Finset.univ (by simp)

@[simp] theorem extendDecisionTreeAt_univ_seed_congr (t : ℕ)
    (T : DecisionTree E) (known known' : ConfigSpace E) :
    extendDecisionTreeAt t T known (Finset.univ : Finset E) =
      extendDecisionTreeAt t T known' Finset.univ := by
  rw [← extendDecisionTreeTriple_leftOrder t T known Finset.univ,
    ← extendDecisionTreeTriple_leftOrder t T known' Finset.univ]
  rw [extendDecisionTreeTriple_univ_seed_congr]

@[simp] theorem extendDecisionTreeAt_zero (T : DecisionTree E)
    (known : ConfigSpace E) (R : Finset E) :
    extendDecisionTreeAt 0 T known R = extendDecisionTree T known R := by
  induction T generalizing known R with
  | leaf b => rfl
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeAt, extendDecisionTree]
      by_cases he : e ∈ R
      · simp [he, ihc, iho]
      · simp [he]
        split <;> simp_all

theorem extendDecisionTreeAt_eq_allIndependent_of_card_le (t : ℕ)
    (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E)
    (hcard : R.card ≤ t) :
    extendDecisionTreeAt t T known R =
      allIndependent (extendDecisionTree T known R) := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeAt, extendDecisionTree]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeAt, extendDecisionTree]
      by_cases he : e ∈ R
      · simp only [he, dif_pos, allIndependent]
        have ht : 0 < t := by
          have hRpos : 0 < R.card := Finset.card_pos.mpr ⟨e, he⟩
          omega
        have hchild : (R.erase e).card ≤ t - 1 := by
          rw [Finset.card_erase_of_mem he]
          omega
        simp only [ht, decide_true]
        rw [ihc (t - 1) (Function.update known e false) (R.erase e) hchild]
        rw [iho (t - 1) (Function.update known e true) (R.erase e) hchild]
      · simp only [he, dif_neg]
        by_cases hb : known e
        · simp only [hb, if_true]
          exact iho t known R hcard
        · simp only [hb, Bool.false_eq_true, if_false]
          exact ihc t known R hcard

@[simp] theorem extendDecisionTreeAt_card_univ_eq_allIndependent
    (T : DecisionTree E) (known : ConfigSpace E) :
    extendDecisionTreeAt (Fintype.card E) T known (Finset.univ : Finset E) =
      allIndependent (extendDecisionTree T known Finset.univ) := by
  apply extendDecisionTreeAt_eq_allIndependent_of_card_le
  simp


theorem sharedEdges_extendDecisionTreeAt_eq_empty_of_card_le (t : ℕ)
    (T : DecisionTree E) (known base : ConfigSpace E) (R : Finset E)
    (hknown : ∀ z, z ∉ R → known z = base z) (hcard : R.card ≤ t) :
    sharedEdges (extendDecisionTreeAt t T known R) base = ∅ := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      rw [extendDecisionTreeAt]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        have ht : 0 < t := by
          have hRpos : 0 < R.card := Finset.card_pos.mpr ⟨e, he⟩
          omega
        have hchild : (R.erase e).card ≤ t - 1 := by
          rw [Finset.card_erase_of_mem he]
          omega
        by_cases hb : base e
        · simp only [sharedEdges, hb, if_true, ht, decide_true]
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e true z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb]
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          exact iho (t - 1) (Function.update known e true) (R.erase e) hk hchild
        · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
          simp only [sharedEdges, hb, Bool.false_eq_true, if_false, ht, decide_true]
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e false z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb']
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          exact ihc (t - 1) (Function.update known e false) (R.erase e) hk hchild
      · rw [dif_neg he]
        have hkb : known e = base e := hknown e he
        by_cases hb : base e
        · simp only [hkb, hb, if_true]
          exact iho t known R hknown hcard
        · simp only [hkb, hb, Bool.false_eq_true, if_false]
          exact ihc t known R hknown hcard

@[simp] theorem sharedEdges_extendDecisionTreeAt_card_univ (T : DecisionTree E)
    (known base : ConfigSpace E) :
    sharedEdges (extendDecisionTreeAt (Fintype.card E) T known
      (Finset.univ : Finset E)) base = ∅ := by
  apply sharedEdges_extendDecisionTreeAt_eq_empty_of_card_le
  · simp
  · simp


theorem sharedEdges_extendDecisionTreeAt_succ_subset (t : ℕ)
    (T : DecisionTree E) (known base : ConfigSpace E) (R : Finset E)
    (hknown : ∀ z, z ∉ R → known z = base z) :
    sharedEdges (extendDecisionTreeAt (t + 1) T known R) base ⊆
      sharedEdges (extendDecisionTreeAt t T known R) base := by
  induction T generalizing t known R with
  | leaf b => simp [extendDecisionTreeAt]
  | node e opened closed iho ihc =>
      simp only [extendDecisionTreeAt]
      by_cases he : e ∈ R
      · simp only [he, dif_pos]
        by_cases hb : base e
        · have hk : ∀ z, z ∉ R.erase e →
              Function.update known e true z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb]
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          cases t with
          | zero => simp [sharedEdges, hb]
          | succ t =>
              simpa [sharedEdges, hb, Nat.add_assoc] using
                iho t (Function.update known e true) (R.erase e) hk
        · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e false z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb']
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          cases t with
          | zero => simp [sharedEdges, hb]
          | succ t =>
              simpa [sharedEdges, hb, Nat.add_assoc] using
                ihc t (Function.update known e false) (R.erase e) hk
      · simp only [he, dif_neg]
        have hkb : known e = base e := hknown e he
        by_cases hb : base e
        · simp only [hkb, hb, if_true]
          exact iho t known R hknown
        · simp only [hkb, hb, Bool.false_eq_true, if_false]
          exact ihc t known R hknown

end AdaptiveCausalKernel
end OSSS
end StatMech
