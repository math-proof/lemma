/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part16


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem choiceExecValid_tail
    (R : Nat) (p : IsingLeapfrogBox R) (b : Bool × Bool)
    (bs : List (Bool × Bool))
    (h : IsingLeapfrogChoiceExecValid R p (b :: bs)) :
    IsingLeapfrogChoiceExecValid R (isingLeapfrogChoiceNext R p b) bs := by
  intro j hj
  have hmain := h (j + 1) (by simpa using hj)
  simpa [isingLeapfrogChoiceRun, List.take_succ_cons] using hmain

theorem choiceExecValid_start
    (R : Nat) (p : IsingLeapfrogBox R) (b : Bool × Bool)
    (bs : List (Bool × Bool))
    (h : IsingLeapfrogChoiceExecValid R p (b :: bs)) :
    ¬ isingLeapfrogBoxBoundary R p := by
  have h0 := h 0 (by simp)
  simpa [isingLeapfrogChoiceRun] using h0

theorem choiceExecValid_run_boxInt_eq_endpoint
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogChoiceExecValid R p bs) :
    isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p bs) =
      isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps bs) := by
  induction bs generalizing p with
  | nil =>
      simp [isingLeapfrogChoiceRun, isingLeapfrogChoiceSteps,
        isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      rw [show isingLeapfrogChoiceRun R p (b :: bs) =
          isingLeapfrogChoiceRun R (isingLeapfrogChoiceNext R p b) bs by rfl]
      rw [ih (isingLeapfrogChoiceNext R p b)
        (choiceExecValid_tail R p b bs h)]
      rw [isingLeapfrogBoxInt_choiceNext_full R p b
        (choiceExecValid_start R p b bs h)]
      unfold isingLeapfrogChoiceSteps isingDiagonalWalkEndpoint
        isingDiagonalWalkNext isingDiagonalWalkDisplacement
      apply Prod.ext <;> simp <;> ring

theorem couplingChoiceTransform_drop_of_some
    (t : Nat) (start : Int × Int) (level : Int)
    (w : IsingLeapfrogChoiceStringFamily t)
    (split : IsingDiagonalWalkHitSplit start level)
    (hsplit : isingDiagonalWalkFirstHitSplit? start level
      (isingLeapfrogChoiceSteps w.1) = some split) :
    (isingLeapfrogCouplingChoiceTransform t start level w).1.drop
        split.before.length = w.1.drop split.before.length := by
  have hwencode : isingLeapfrogEncodeSteps
      (isingLeapfrogChoiceSteps w.1) = w.1 := encodeSteps_choiceSteps w.1
  unfold isingLeapfrogCouplingChoiceTransform
  dsimp only
  unfold isingDiagonalWalkCouplingReflectSteps
  rw [hsplit]
  rw [← firstHitSplit_steps hsplit] at hwencode
  unfold isingLeapfrogEncodeSteps at hwencode ⊢
  rw [← hwencode]
  simp [IsingDiagonalWalkHitSplit.steps, reflectPrefix]

theorem couplingChoiceTransform_take_steps_of_some
    (t : Nat) (start : Int × Int) (level : Int)
    (w : IsingLeapfrogChoiceStringFamily t)
    (split : IsingDiagonalWalkHitSplit start level)
    (hsplit : isingDiagonalWalkFirstHitSplit? start level
      (isingLeapfrogChoiceSteps w.1) = some split) :
    isingLeapfrogChoiceSteps
      ((isingLeapfrogCouplingChoiceTransform t start level w).1.take
        split.before.length) = split.before.map reflectIncrement := by
  rw [isingLeapfrogChoiceSteps, List.map_take]
  have hsteps : isingLeapfrogChoiceSteps
      (isingLeapfrogCouplingChoiceTransform t start level w).1 =
      isingDiagonalWalkCouplingReflectSteps start level
        (isingLeapfrogChoiceSteps w.1) := by
    exact choiceSteps_encodeSteps_of_valid _
      (couplingReflectSteps_valid start level _
        (isingLeapfrogChoiceSteps_valid w.1))
  change (isingLeapfrogChoiceSteps
    (isingLeapfrogCouplingChoiceTransform t start level w).1).take
      split.before.length = split.before.map reflectIncrement
  rw [hsteps]
  unfold isingDiagonalWalkCouplingReflectSteps
  rw [hsplit]
  simp [IsingDiagonalWalkHitSplit.steps, reflectPrefix]

theorem choiceSteps_take_of_split
    (t : Nat) (start : Int × Int) (level : Int)
    (w : IsingLeapfrogChoiceStringFamily t)
    (split : IsingDiagonalWalkHitSplit start level)
    (hsplit : isingDiagonalWalkFirstHitSplit? start level
      (isingLeapfrogChoiceSteps w.1) = some split) :
    isingLeapfrogChoiceSteps (w.1.take split.before.length) = split.before := by
  have hs := firstHitSplit_steps hsplit
  have ht := congrArg (fun z : List (Int × Int) =>
    z.take split.before.length) hs
  simpa [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
    List.map_take] using ht.symm


theorem stoppedCoupling_endpoints_eq_of_execValid_to_hit
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (w : IsingLeapfrogChoiceStringFamily t)
    (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level)
    (hsplit : isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1) = some split)
    (hsource : IsingLeapfrogChoiceExecValid R p
      (w.1.take split.before.length))
    (hmirrorValid : IsingLeapfrogChoiceExecValid R p'
      ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
        level w).1.take split.before.length)) :
    isingLeapfrogChoiceRun R p w.1 =
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1 := by
  let w' := isingLeapfrogCouplingChoiceTransform t
    (isingLeapfrogBoxInt p) level w
  let k := split.before.length
  have hsourceSteps := choiceSteps_take_of_split t (isingLeapfrogBoxInt p)
    level w split hsplit
  have hmirrorSteps := couplingChoiceTransform_take_steps_of_some t
    (isingLeapfrogBoxInt p) level w split hsplit
  have hsourceEnd := choiceExecValid_run_boxInt_eq_endpoint R p
    (w.1.take k) hsource
  have hmirrorEnd := choiceExecValid_run_boxInt_eq_endpoint R p'
    (w'.1.take k) hmirrorValid
  have hfreeEnd : isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      split.before =
    isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
      (split.before.map reflectIncrement) := by
    rw [hmirror]
    apply Prod.ext
    · have h := reflectPrefix_endpoint_take_fst_of_le_before split k (le_refl _)
      have hhit : (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
          split.before).1 = level := by
        simpa [isingDiagonalWalkEndpoint] using split.hit
      have h' : (isingDiagonalWalkEndpoint
          (reflectedEndpoint level (isingLeapfrogBoxInt p))
            (split.before.map reflectIncrement)).1 =
          2 * level - (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            split.before).1 := by
        simpa [k, IsingDiagonalWalkHitSplit.steps, reflectPrefix] using h
      rw [h']
      omega
    · have h := reflectPrefix_endpoint_take_snd_of_le_before split k (le_refl _)
      simpa [k, IsingDiagonalWalkHitSplit.steps, reflectPrefix] using h.symm
  have hrunPrefix : isingLeapfrogChoiceRun R p (w.1.take k) =
      isingLeapfrogChoiceRun R p' (w'.1.take k) := by
    apply isingLeapfrogBoxInt_injective
    rw [hsourceEnd, hmirrorEnd, hsourceSteps, hmirrorSteps]
    exact hfreeEnd
  have hdrop := couplingChoiceTransform_drop_of_some t
    (isingLeapfrogBoxInt p) level w split hsplit
  rw [← List.take_append_drop k w.1,
    ← List.take_append_drop k w'.1,
    isingLeapfrogChoiceRun_append_full,
    isingLeapfrogChoiceRun_append_full,
    hrunPrefix, hdrop]


end
end StatMech.Universality
