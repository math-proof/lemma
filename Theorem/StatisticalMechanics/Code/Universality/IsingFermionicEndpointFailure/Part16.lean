/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part19


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem mirrorFailureAtAlignedOrResidualCover_value
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (w : IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) :
    endpointFailureAlignedOrResidualValue R t p p' q level
      (mirrorFailureAtAlignedOrResidualCover R t p p' q level w) = w.1 := by
  exact Classical.choose_spec
    (exists_mirrorFailureAtAlignedOrResidualCover R t p p' q level w)

theorem mirrorFailureAtAlignedOrResidualCover_injective
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Function.Injective
      (mirrorFailureAtAlignedOrResidualCover R t p p' q level) := by
  intro a b hab
  apply Subtype.ext
  rw [← mirrorFailureAtAlignedOrResidualCover_value R t p p' q level a,
    ← mirrorFailureAtAlignedOrResidualCover_value R t p p' q level b, hab]

theorem natCard_mirrorFailureAt_le_aligned_add_residual
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) <=
      Nat.card (IsingSourceFailureOutputAtFamily R t p q level) +
        Nat.card (IsingMirrorFailureOutputAtFamily R t p p' q level) +
        Nat.card (IsingMirrorOnlySourceOutputAtFamily R t p p' q level) := by
  calc
    _ <= Nat.card (Sum (IsingSourceFailureOutputAtFamily R t p q level)
        (Sum (IsingMirrorFailureOutputAtFamily R t p p' q level)
          (IsingMirrorOnlySourceOutputAtFamily R t p p' q level))) :=
      Nat.card_le_card_of_injective
        (mirrorFailureAtAlignedOrResidualCover R t p p' q level)
        (mirrorFailureAtAlignedOrResidualCover_injective R t p p' q level)
    _ = _ := by rw [Nat.card_sum, Nat.card_sum]; omega

theorem choiceRun_boundary_output_data_endpointFailure
    (R t : Nat) (p q : IsingLeapfrogBox R)
    (hq : isingLeapfrogBoxBoundary R q)
    (w : IsingLeapfrogChoiceStringFamily t)
    (hout : isingLeapfrogChoiceRun R p w.1 = q) :
    exists k, k <= t /\
      isingLeapfrogChoiceRun R p (w.1.take k) = q /\
      forall l, l < k -> ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.take l)) := by
  let hex : exists k, k <= t /\ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.take k)) := by
    refine ⟨t, le_refl _, ?_⟩
    have ht : w.1.take t = w.1 := by
      simpa [w.2] using (List.take_all w.1)
    rw [ht, hout]
    exact hq
  let k := Nat.find hex
  have hkSpec := Nat.find_spec hex
  have hminimal : forall l, l < k -> ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.take l)) := by
    intro l hl hb
    exact Nat.find_min hex hl ⟨by omega, hb⟩
  have hkOutput : isingLeapfrogChoiceRun R p (w.1.take k) = q := by
    have hdecomp : w.1 = w.1.take k ++ w.1.drop k :=
      (List.take_append_drop k w.1).symm
    have hfull : isingLeapfrogChoiceRun R p w.1 =
        isingLeapfrogChoiceRun R p (w.1.take k) := by
      calc
        _ = isingLeapfrogChoiceRun R p (w.1.take k ++ w.1.drop k) := by
          rw [← hdecomp]
        _ = isingLeapfrogChoiceRun R
            (isingLeapfrogChoiceRun R p (w.1.take k)) (w.1.drop k) :=
          isingLeapfrogChoiceRun_append_full ..
        _ = _ := isingLeapfrogChoiceRun_of_boundary_endpointFailure R _
          hkSpec.2 _
    exact hfull.symm.trans hout
  exact ⟨k, hkSpec.1, hkOutput, hminimal⟩

theorem mirrorOnly_firstBoundary_right
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) :
    exists (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p)
        (level : Int)) (j : Nat),
      isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) (level : Int)
        (isingLeapfrogChoiceSteps w.1.1) = some split /\
      j < split.before.length /\
      (isingLeapfrogChoiceRun R p'
        ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
          (level : Int) w.1).1.take j)).1.1 = R /\
      ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
        2 * (level : Int) - R /\
      (forall l, l < j ->
        2 * (level : Int) - R <
            ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) /\
          ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) < level) /\
      (forall l, l < j -> ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p'
          ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
            (level : Int) w.1).1.take l))) /\
      IsingLeapfrogChoiceExecValid R p (w.1.1.take split.before.length) := by
  rcases w.2.1 with ⟨split, hsplit, hmirrorNotValid⟩
  have hsourceValid : IsingLeapfrogChoiceExecValid R p
      (w.1.1.take split.before.length) := by
    by_contra hnot
    exact w.2.2.1 ⟨split, hsplit, hnot⟩
  let w' := isingLeapfrogCouplingChoiceTransform t
    (isingLeapfrogBoxInt p) (level : Int) w.1
  have hex : exists j, j < (w'.1.take split.before.length).length /\
      isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p' ((w'.1.take split.before.length).take j)) := by
    unfold IsingLeapfrogChoiceExecValid at hmirrorNotValid
    push_neg at hmirrorNotValid
    exact hmirrorNotValid
  let j := Nat.find hex
  have hjSpec := Nat.find_spec hex
  have hbeforeT : split.before.length <= t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
      w.1.2] at hlen
    omega
  have hj : j < split.before.length := by
    have hj' := hjSpec.1
    change j < (w'.1.take split.before.length).length at hj'
    rw [List.length_take] at hj'
    have hw' : (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).1.length = t :=
      (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) (level : Int) w.1).2
    change w'.1.length = t at hw'
    omega
  have hmirrorBoundary : isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p' (w'.1.take j)) := by
    have hb := hjSpec.2
    change isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p' ((w'.1.take split.before.length).take j)) at hb
    simpa [List.take_take, Nat.min_eq_left hj.le] using hb
  have hmirrorMinimal : forall r, r < j ->
      ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p' (w'.1.take r)) := by
    intro r hr hb
    apply Nat.find_min hex hr
    refine ⟨?_, ?_⟩
    · rw [List.length_take]
      have hw' : w'.1.length = t := w'.2
      omega
    · simpa [List.take_take,
        Nat.min_eq_left (show r <= split.before.length by omega)] using hb
  have hmirrorValidJ : IsingLeapfrogChoiceExecValid R p' (w'.1.take j) := by
    intro r hr
    have hrj : r < j := by
      rw [List.length_take] at hr
      omega
    simpa [List.take_take, Nat.min_eq_left hrj.le] using
      hmirrorMinimal r hrj
  have hsourceValidJ : IsingLeapfrogChoiceExecValid R p (w.1.1.take j) := by
    intro r hr
    have hrj : r < j := by
      rw [List.length_take] at hr
      omega
    have hs := hsourceValid r (by
      rw [List.length_take]
      have hw : w.1.1.length = t := w.1.2
      omega)
    simpa [List.take_take, Nat.min_eq_left hrj.le,
      Nat.min_eq_left (show r <= split.before.length by omega)] using hs
  have hvalid : split.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsplit]
    exact isingLeapfrogChoiceSteps_valid w.1.1
  have hsourceLt := (firstHitSplit_firstHit hsplit).endpoint_take_fst_lt
    split hvalid (by omega : (isingLeapfrogBoxInt p).1 < (level : Int)) j hj
  have hsourceBeforeSteps : split.before.take j =
      isingLeapfrogChoiceSteps (w.1.1.take j) := by
    have hs := congrArg (fun path : List (Int × Int) => path.take j)
      (firstHitSplit_steps hsplit)
    simpa [IsingDiagonalWalkHitSplit.steps,
      List.take_append_of_le_length hj.le,
      isingLeapfrogChoiceSteps, List.map_take] using hs
  rw [hsourceBeforeSteps] at hsourceLt
  have hsourceSteps : split.steps.take j =
      isingLeapfrogChoiceSteps (w.1.1.take j) := by
    have hs := congrArg (fun path : List (Int × Int) => path.take j)
      (firstHitSplit_steps hsplit)
    simpa [isingLeapfrogChoiceSteps, List.map_take] using hs
  have hsourceRun := choiceExecValid_run_boxInt_eq_endpoint R p
    (w.1.1.take j) hsourceValidJ
  have hmirrorRun := choiceExecValid_run_boxInt_eq_endpoint R p'
    (w'.1.take j) hmirrorValidJ
  have hbeforeSteps := couplingChoiceTransform_take_steps_of_some t
    (isingLeapfrogBoxInt p) (level : Int) w.1 split hsplit
  have hmirrorSteps : isingLeapfrogChoiceSteps (w'.1.take j) =
      split.reflectPrefix.steps.take j := by
    calc
      _ = (isingLeapfrogChoiceSteps (w'.1.take split.before.length)).take j := by
        simp [isingLeapfrogChoiceSteps, List.map_take, List.take_take,
          Nat.min_eq_left hj.le]
      _ = (split.before.map reflectIncrement).take j := by rw [hbeforeSteps]
      _ = _ := by
        unfold IsingDiagonalWalkHitSplit.reflectPrefix
          IsingDiagonalWalkHitSplit.steps
        rw [List.take_append_of_le_length (by simpa using hj.le)]
  have hmx := congrArg Prod.fst hmirrorRun
  change ((isingLeapfrogChoiceRun R p' (w'.1.take j)).1.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
      (isingLeapfrogChoiceSteps (w'.1.take j))).1 at hmx
  rw [hmirror, hmirrorSteps,
    reflectPrefix_endpoint_take_fst_of_le_before split j hj.le,
    hsourceSteps] at hmx
  have hmy := congrArg Prod.snd hmirrorRun
  change ((isingLeapfrogChoiceRun R p' (w'.1.take j)).2.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
      (isingLeapfrogChoiceSteps (w'.1.take j))).2 at hmy
  rw [hmirror, hmirrorSteps,
    reflectPrefix_endpoint_take_snd_of_le_before split j hj.le,
    hsourceSteps] at hmy
  have hsx := congrArg Prod.fst hsourceRun
  have hsy := congrArg Prod.snd hsourceRun
  change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps (w.1.1.take j))).1 at hsx
  change ((isingLeapfrogChoiceRun R p (w.1.1.take j)).2.1 : Int) =
    (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps (w.1.1.take j))).2 at hsy
  have hsourceBetween : forall l, l < j ->
      2 * (level : Int) - R <
          ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) /\
        ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) < level := by
    intro l hl
    have hlBefore : l < split.before.length := hl.trans hj
    have hsourceValidL : IsingLeapfrogChoiceExecValid R p (w.1.1.take l) := by
      intro r hr
      have hrl : r < l := by
        rw [List.length_take] at hr
        omega
      have hs := hsourceValid r (by
        rw [List.length_take]
        have hw : w.1.1.length = t := w.1.2
        omega)
      change ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p ((w.1.1.take l).take r))
      change ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p
          ((w.1.1.take split.before.length).take r)) at hs
      rw [List.take_take, Nat.min_eq_left hrl.le]
      rw [List.take_take,
        Nat.min_eq_left (show r <= split.before.length by omega)] at hs
      exact hs
    have hmirrorValidL : IsingLeapfrogChoiceExecValid R p' (w'.1.take l) := by
      intro r hr
      have hrl : r < l := by
        rw [List.length_take] at hr
        omega
      simpa [List.take_take, Nat.min_eq_left hrl.le] using
        hmirrorMinimal r (hrl.trans hl)
    have hsourceStepsL : split.steps.take l =
        isingLeapfrogChoiceSteps (w.1.1.take l) := by
      have hs := congrArg (fun path : List (Int × Int) => path.take l)
        (firstHitSplit_steps hsplit)
      simpa [isingLeapfrogChoiceSteps, List.map_take] using hs
    have hsourceBeforeStepsL : split.before.take l =
        isingLeapfrogChoiceSteps (w.1.1.take l) := by
      have hs := congrArg (fun path : List (Int × Int) => path.take l)
        (firstHitSplit_steps hsplit)
      simpa [IsingDiagonalWalkHitSplit.steps,
        List.take_append_of_le_length hlBefore.le,
        isingLeapfrogChoiceSteps, List.map_take] using hs
    have hmirrorStepsL : isingLeapfrogChoiceSteps (w'.1.take l) =
        split.reflectPrefix.steps.take l := by
      calc
        _ = (isingLeapfrogChoiceSteps
            (w'.1.take split.before.length)).take l := by
          simp [isingLeapfrogChoiceSteps, List.map_take, List.take_take,
            Nat.min_eq_left hlBefore.le]
        _ = (split.before.map reflectIncrement).take l := by rw [hbeforeSteps]
        _ = _ := by
          unfold IsingDiagonalWalkHitSplit.reflectPrefix
            IsingDiagonalWalkHitSplit.steps
          rw [List.take_append_of_le_length (by simpa using hlBefore.le)]
    have hsourceRunL := choiceExecValid_run_boxInt_eq_endpoint R p
      (w.1.1.take l) hsourceValidL
    have hmirrorRunL := choiceExecValid_run_boxInt_eq_endpoint R p'
      (w'.1.take l) hmirrorValidL
    have hmxL := congrArg Prod.fst hmirrorRunL
    change ((isingLeapfrogChoiceRun R p' (w'.1.take l)).1.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p')
        (isingLeapfrogChoiceSteps (w'.1.take l))).1 at hmxL
    rw [hmirror, hmirrorStepsL,
      reflectPrefix_endpoint_take_fst_of_le_before split l hlBefore.le,
      hsourceStepsL] at hmxL
    have hsxL := congrArg Prod.fst hsourceRunL
    change ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.1.take l))).1 at hsxL
    have hmirrorNot := hmirrorMinimal l hl
    have hmirrorLtR : ((isingLeapfrogChoiceRun R p'
        (w'.1.take l)).1.1 : Int) < R := by
      have hle : (isingLeapfrogChoiceRun R p' (w'.1.take l)).1.1 <= R := by
        omega
      have hne : (isingLeapfrogChoiceRun R p' (w'.1.take l)).1.1 ≠ R := by
        intro heq
        apply hmirrorNot
        unfold isingLeapfrogBoxBoundary
        right; left
        omega
      exact_mod_cast (lt_of_le_of_ne hle hne)
    have hsourceLtL := (firstHitSplit_firstHit hsplit).endpoint_take_fst_lt
      split hvalid (by omega : (isingLeapfrogBoxInt p).1 < (level : Int))
      l hlBefore
    rw [hmxL, ← hsxL] at hmirrorLtR
    rw [hsourceBeforeStepsL, ← hsxL] at hsourceLtL
    exact ⟨by omega, hsourceLtL⟩
  unfold isingLeapfrogBoxBoundary at hmirrorBoundary
  rcases hmirrorBoundary with hx0 | hxR | hy0 | hyR
  · exfalso
    have hmirrorZero : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).1.1 : Int) = 0 := by exact_mod_cast hx0
    have hsourceNonneg : 0 <= ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).1.1 : Int) := by positivity
    rw [hmx, ← hsx] at hmirrorZero
    omega
  · refine ⟨split, j, hsplit, hj, ?_, ?_, hsourceBetween, ?_, hsourceValid⟩
    · have hxRNat : (isingLeapfrogChoiceRun R p' (w'.1.take j)).1.1 = R := by
        omega
      simpa [w'] using hxRNat
    · have hmirrorR : ((isingLeapfrogChoiceRun R p'
          (w'.1.take j)).1.1 : Int) = R := by
        have hxRNat : (isingLeapfrogChoiceRun R p' (w'.1.take j)).1.1 = R := by
          omega
        exact_mod_cast hxRNat
      rw [hmx, ← hsx] at hmirrorR
      omega
    · intro l hl
      simpa [w'] using hmirrorMinimal l hl
  · exfalso
    have hmirrorY : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).2.1 : Int) = 0 := by exact_mod_cast hy0
    have hsourceY : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).2.1 : Int) = 0 := by
      rw [hmy, ← hsy] at hmirrorY
      exact hmirrorY
    have hsourceBoundary : isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.1.take j)) := by
      unfold isingLeapfrogBoxBoundary
      right; right; left
      exact_mod_cast hsourceY
    exact (hsourceValid j (by
      rw [List.length_take]
      have hw : w.1.1.length = t := w.1.2
      omega)) (by
      simpa [List.take_take, Nat.min_eq_left hj.le] using hsourceBoundary)
  · exfalso
    have hmirrorYNat : (isingLeapfrogChoiceRun R p'
        (w'.1.take j)).2.1 = R := by omega
    have hmirrorY : ((isingLeapfrogChoiceRun R p'
        (w'.1.take j)).2.1 : Int) = R := by exact_mod_cast hmirrorYNat
    have hsourceY : ((isingLeapfrogChoiceRun R p
        (w.1.1.take j)).2.1 : Int) = R := by
      rw [hmy, ← hsy] at hmirrorY
      exact hmirrorY
    have hsourceYNat : (isingLeapfrogChoiceRun R p
        (w.1.1.take j)).2.1 = R := by exact_mod_cast hsourceY
    have hsourceBoundary : isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.1.take j)) := by
      unfold isingLeapfrogBoxBoundary
      right; right; right
      omega
    exact (hsourceValid j (by
      rw [List.length_take]
      have hw : w.1.1.length = t := w.1.2
      omega)) (by
      simpa [List.take_take, Nat.min_eq_left hj.le] using hsourceBoundary)


theorem mirrorOnly_ordered_boundary_marks
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q)
    (w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) :
    exists (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p)
        (level : Int)) (j k : Nat),
      isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) (level : Int)
        (isingLeapfrogChoiceSteps w.1.1) = some split /\
      j < k /\ k <= t /\
      (isingLeapfrogChoiceRun R p'
        ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
          (level : Int) w.1).1.take j)).1.1 = R /\
      ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) =
        2 * (level : Int) - R /\
      (forall l, l < j ->
        2 * (level : Int) - R <
            ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) /\
          ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) < level) /\
      (forall l, l < j -> ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p'
          ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
            (level : Int) w.1).1.take l))) /\
      isingLeapfrogChoiceRun R p (w.1.1.take k) = q /\
      (forall l, l < k -> ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogChoiceRun R p (w.1.1.take l))) := by
  rcases mirrorOnly_firstBoundary_right R level t p p' q hstart hmirror w with
    ⟨split, j, hsplit, hj, hjRight, hjSource, hjBetween, hjMinimal,
      hsourceValid⟩
  rcases choiceRun_boundary_output_data_endpointFailure R t p q hq w.1
    w.2.2.2 with ⟨k, hkT, hkOutput, hkMinimal⟩
  have hjk : j < k := by
    by_contra hnot
    have hkj : k <= j := by omega
    have hbeforeT : split.before.length <= t := by
      have hlen := congrArg List.length (firstHitSplit_steps hsplit)
      simp [IsingDiagonalWalkHitSplit.steps, isingLeapfrogChoiceSteps,
        w.1.2] at hlen
      omega
    have hsourceNotBoundary := hsourceValid k (by
      rw [List.length_take]
      rw [w.1.2]
      omega)
    apply hsourceNotBoundary
    have hq' := hq
    rw [← hkOutput] at hq'
    simpa [List.take_take, Nat.min_eq_left (hkj.trans hj.le)] using hq'
  exact ⟨split, j, k, hsplit, hjk, hkT, hjRight, hjSource, hjBetween,
    hjMinimal,
    hkOutput, hkMinimal⟩

theorem choiceRun_take_coordinates_eq_lineFree
    (R t k : Nat) (p : IsingLeapfrogBox R)
    (w : IsingLeapfrogChoiceStringFamily t)
    (hkT : k <= t)
    (hminimal : forall l, l < k -> ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (w.1.take l)))
    (l : Nat) (hl : l <= k) :
    ((isingLeapfrogChoiceRun R p (w.1.take l)).1.1 : Int) =
        lineFreeEndpoint (isingLeapfrogBoxInt p).1
          ((w.1.take l).map Prod.fst) /\
      ((isingLeapfrogChoiceRun R p (w.1.take l)).2.1 : Int) =
        lineFreeEndpoint (isingLeapfrogBoxInt p).2
          ((w.1.take l).map Prod.snd) := by
  have hvalid : IsingLeapfrogChoiceExecValid R p (w.1.take l) := by
    intro r hr
    have hrl : r < l := by
      rw [List.length_take, w.2] at hr
      omega
    have hmain := hminimal r (hrl.trans_le hl)
    simpa [List.take_take, Nat.min_eq_left hrl.le] using hmain
  have hrun := choiceExecValid_run_boxInt_eq_endpoint R p (w.1.take l) hvalid
  constructor
  · have hx := congrArg Prod.fst hrun
    change ((isingLeapfrogChoiceRun R p (w.1.take l)).1.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.take l))).1 at hx
    rw [← lineFreeEndpoint_choiceHorizontal_full] at hx
    exact hx
  · have hy := congrArg Prod.snd hrun
    change ((isingLeapfrogChoiceRun R p (w.1.take l)).2.1 : Int) =
      (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps (w.1.take l))).2 at hy
    rw [← lineFreeEndpoint_choiceVertical_full] at hy
    exact hy

end
end StatMech.Universality
