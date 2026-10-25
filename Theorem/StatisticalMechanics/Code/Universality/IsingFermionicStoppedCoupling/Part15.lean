/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part19


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem stoppedCouplingBadCoverValue_apply
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (w : IsingLeapfrogStoppedCouplingBadFamily R t p p' level) :
    stoppedCouplingBadCoverValue R t p p' level
      (stoppedCouplingBadCover R t p p' level hmirror w) = w.1 := by
  classical
  unfold stoppedCouplingBadCover
  by_cases hn : ∀ k, k ≤ t →
      lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.1.map Prod.fst).take k) ≠ level
  · rw [dif_pos hn]
    rfl
  · rw [dif_neg hn]
    by_cases hs : IsingStoppedCouplingSourceFailure R p level w.1
    · rw [dif_pos hs]
      rfl
    · rw [dif_neg hs]
      rfl

theorem stoppedCouplingBadCover_injective
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    Function.Injective
      (stoppedCouplingBadCover R t p p' level hmirror) := by
  intro a b hab
  apply Subtype.ext
  rw [← stoppedCouplingBadCoverValue_apply R t p p' level hmirror a,
    ← stoppedCouplingBadCoverValue_apply R t p p' level hmirror b, hab]


theorem natCard_stoppedCouplingBad_le_noHit_add_failures
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    Nat.card (IsingLeapfrogStoppedCouplingBadFamily R t p p' level) ≤
      Nat.card (IsingLeapfrogChoiceNoHitAll t
        (isingLeapfrogBoxInt p).1 level) +
      Nat.card (IsingStoppedCouplingSourceFailureFamily R t p level) +
      Nat.card (IsingStoppedCouplingMirrorFailureFamily R t p p' level) := by
  calc
    _ ≤ Nat.card
        (IsingLeapfrogChoiceNoHitAll t (isingLeapfrogBoxInt p).1 level ⊕
          IsingStoppedCouplingSourceFailureFamily R t p level ⊕
            IsingStoppedCouplingMirrorFailureFamily R t p p' level) :=
      Nat.card_le_card_of_injective
        (stoppedCouplingBadCover R t p p' level hmirror)
        (stoppedCouplingBadCover_injective R t p p' level hmirror)
    _ = _ := by rw [Nat.card_sum, Nat.card_sum]; omega


theorem exists_boundary_before_of_not_choiceExecValid
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : ¬ IsingLeapfrogChoiceExecValid R p bs) :
    ∃ j, j < bs.length ∧ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (bs.take j)) := by
  unfold IsingLeapfrogChoiceExecValid at h
  push_neg at h
  exact h


theorem lineChoiceRun_val_eq_lineFreeEndpoint
    (n : Nat) (p : IsingLineBox n) (bs : List Bool)
    (hfree : ∀ j, j < bs.length →
      lineFreeEndpoint (p.1 : Int) (bs.take j) ≠ 0 ∧
        lineFreeEndpoint (p.1 : Int) (bs.take j) ≠ n) :
    ((isingLineChoiceRun n p bs).1 : Int) =
      lineFreeEndpoint (p.1 : Int) bs := by
  induction bs generalizing p with
  | nil => simp [isingLineChoiceRun, lineFreeEndpoint]
  | cons b bs ih =>
      have h0 := hfree 0 (by simp)
      have hp0 : p.1 ≠ 0 := by
        intro hp0
        apply h0.1
        simp [lineFreeEndpoint, hp0]
      have hpn : p.1 ≠ n := by
        intro hpn
        apply h0.2
        simp [lineFreeEndpoint, hpn]
      have hp : ¬ isingLineBoxBoundary n p := by
        exact fun h => h.elim hp0 hpn
      have hpPos : 0 < p.1 := by omega
      have hwestCast : ((p.1 - 1 : Nat) : Int) = (p.1 : Int) - 1 := by
        omega
      have htail : ∀ j, j < bs.length →
          lineFreeEndpoint
              ((isingLineChoiceNext n p b).1 : Int) (bs.take j) ≠ 0 ∧
            lineFreeEndpoint
              ((isingLineChoiceNext n p b).1 : Int) (bs.take j) ≠ n := by
        intro j hj
        have hmain := hfree (j + 1) (by simp; omega)
        cases b
        · simpa [isingLineChoiceNext, hp, isingLineWest,
            lineFreeEndpoint, List.take_succ_cons, hwestCast] using hmain
        · simpa [isingLineChoiceNext, hp, isingLineEast,
            lineFreeEndpoint, List.take_succ_cons] using hmain
      rw [show isingLineChoiceRun n p (b :: bs) =
          isingLineChoiceRun n (isingLineChoiceNext n p b) bs by rfl]
      rw [ih (isingLineChoiceNext n p b) htail]
      cases b
      · simp [isingLineChoiceNext, hp, isingLineWest,
          lineFreeEndpoint, hwestCast]
        congr 1 <;> ring
      · simp [isingLineChoiceNext, hp, isingLineEast,
          lineFreeEndpoint]

theorem sourceFailure_boundary_data
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int)
    (hstart : (isingLeapfrogBoxInt p).1 < level)
    (w : IsingStoppedCouplingSourceFailureFamily R t p level) :
    ∃ (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level) (j : Nat),
      isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
        (isingLeapfrogChoiceSteps w.1.1) = some split ∧
      j < split.before.length ∧
      isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.1.take j)) ∧
      (∀ l, l < j → ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.1.take l))) ∧
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.take j))).1 < level ∧
      isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p (w.1.1.take j)) =
        isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          (isingLeapfrogChoiceSteps (w.1.1.take j)) := by
  rcases w.2 with ⟨split, hsplit, hnot⟩
  have hex := exists_boundary_before_of_not_choiceExecValid R p
    (w.1.1.take split.before.length) hnot
  let j := Nat.find hex
  have hjSpec := Nat.find_spec hex
  have hbeforeLe : split.before.length ≤ w.1.1.length := by
    have hs := firstHitSplit_steps hsplit
    have hlen : split.steps.length = w.1.1.length := by
      rw [hs]
      simp [isingLeapfrogChoiceSteps]
    unfold IsingDiagonalWalkHitSplit.steps at hlen
    simp only [List.length_append] at hlen
    omega
  have hj : j < split.before.length := by
    exact lt_of_lt_of_le hjSpec.1 (List.length_take_le ..)
  have hjBoundary := hjSpec.2
  have hminimal : ∀ l, l < j → ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.1.take l)) := by
    intro l hl hb
    have hpred : l < (w.1.1.take split.before.length).length ∧
        isingLeapfrogBoxBoundary R
          (isingLeapfrogChoiceRun R p
            ((w.1.1.take split.before.length).take l)) := by
      constructor
      · rw [List.length_take, Nat.min_eq_left hbeforeLe]
        omega
      · have hlbefore : l ≤ split.before.length := by omega
        rw [List.take_take, Nat.min_eq_left hlbefore]
        exact hb
    exact (Nat.find_min hex hl) hpred
  have hexec : IsingLeapfrogChoiceExecValid R p (w.1.1.take j) := by
    intro l hl
    rw [List.length_take, Nat.min_eq_left (by omega)] at hl
    simpa [List.take_take, Nat.min_eq_left hl.le] using hminimal l hl
  have hrun := choiceExecValid_run_boxInt_eq_endpoint R p (w.1.1.take j) hexec
  have hstepsTake : isingLeapfrogChoiceSteps (w.1.1.take j) =
      split.before.take j := by
    have hs := firstHitSplit_steps hsplit
    have ht := congrArg (fun z : List (Int × Int) => z.take j) hs
    simpa [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      List.map_take, List.take_append_of_le_length hj.le] using ht.symm
  have hjFind : Nat.find hex ≤ split.before.length := by
    simpa [j] using hj.le
  have hjBoundaryRaw : isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.1.take j)) := by
    have hb := hjBoundary
    rw [List.take_take, Nat.min_eq_left hjFind] at hb
    simpa [j] using hb
  have hvalid : split.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsplit]
    exact isingLeapfrogChoiceSteps_valid w.1.1
  have hxlt := (firstHitSplit_firstHit hsplit).endpoint_take_fst_lt split
    hvalid hstart j hj
  refine ⟨split, j, hsplit, hj, ?_, hminimal, ?_, hrun⟩
  · exact hjBoundaryRaw
  · rw [hstepsTake]
    exact hxlt

theorem lineFreeEndpoint_choiceVertical_full
    (bs : List (Bool × Bool)) (start : Int × Int) :
    lineFreeEndpoint start.2 (bs.map Prod.snd) =
      (isingDiagonalWalkEndpoint start
        (isingLeapfrogChoiceSteps bs)).2 := by
  induction bs generalizing start with
  | nil =>
      simp [lineFreeEndpoint, isingLeapfrogChoiceSteps,
        isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      have hih := ih (isingDiagonalWalkNext start
        (isingLeapfrogChoiceStep b))
      rcases b with ⟨bx, byy⟩
      cases bx <;> cases byy <;>
        simp [lineFreeEndpoint, isingLeapfrogChoiceSteps,
          isingLeapfrogChoiceStep, isingDiagonalWalkEndpoint,
          isingDiagonalWalkNext, isingDiagonalWalkDisplacement,
          add_assoc] at hih ⊢ <;> linarith

theorem lineFreeEndpoint_translate
    (bs : List Bool) (a b : Int) :
    lineFreeEndpoint b bs = b + (lineFreeEndpoint a bs - a) := by
  induction bs generalizing a b with
  | nil => simp [lineFreeEndpoint]
  | cons x bs ih =>
      cases x
      · change lineFreeEndpoint (b - 1) bs =
          b + (lineFreeEndpoint (a - 1) bs - a)
        rw [ih (a - 1) (b - 1)]
        ring
      · change lineFreeEndpoint (b + 1) bs =
          b + (lineFreeEndpoint (a + 1) bs - a)
        rw [ih (a + 1) (b + 1)]
        ring

theorem prodBits_zip_self (bs : List (Bool × Bool)) :
    (bs.map Prod.fst).zip (bs.map Prod.snd) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [ih]


end
end StatMech.Universality
