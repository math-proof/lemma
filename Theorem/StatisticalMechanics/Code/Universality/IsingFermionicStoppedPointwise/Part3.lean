/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3


namespace StatMech.Universality

open IsingDiagonalWalkHitSplit

theorem stoppedCouplingBadAtCoverValue_apply
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (w : IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) :
    stoppedCouplingBadAtCoverValue R t p p' q level
      (stoppedCouplingBadAtCover R t p p' q level hmirror w) = w.1 := by
  classical
  by_cases hn : forall k, k <= t ->
      lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.1.map Prod.fst).take k) ≠ level
  · unfold stoppedCouplingBadAtCover
    dsimp only
    rw [dif_pos (by
      intro k hk
      exact hn k hk)]
    rfl
  · by_cases hs : IsingStoppedCouplingSourceFailure R p level w.1
    · unfold stoppedCouplingBadAtCover
      dsimp only
      rw [dif_neg (by
        intro h
        apply hn
        intro k hk
        exact h k hk), dif_pos hs]
      rfl
    · unfold stoppedCouplingBadAtCover
      dsimp only
      rw [dif_neg (by
        intro h
        apply hn
        intro k hk
        exact h k hk), dif_neg hs]
      rfl

theorem stoppedCouplingBadAtCover_injective
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    Function.Injective
      (stoppedCouplingBadAtCover R t p p' q level hmirror) := by
  intro a b hab
  apply Subtype.ext
  rw [<- stoppedCouplingBadAtCoverValue_apply R t p p' q level hmirror a,
    <- stoppedCouplingBadAtCoverValue_apply R t p p' q level hmirror b,
    hab]


theorem natCard_stoppedCouplingBadAt_le_endpointFailures
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    Nat.card
        (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) <=
      Nat.card (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) +
      Nat.card
          (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level) +
        Nat.card
          (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) := by
  calc
    _ <= Nat.card
        (Sum (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level)
          (Sum
            (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level)
            (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level))) :=
      Nat.card_le_card_of_injective
        (stoppedCouplingBadAtCover R t p p' q level hmirror)
        (stoppedCouplingBadAtCover_injective R t p p' q level hmirror)
    _ = _ := by rw [Nat.card_sum, Nat.card_sum]; omega


theorem isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (C : Real)
    (hfail :
      ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingSourceFailureAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
            R t p p' q level) : Nat) : Real) / (4 : Real) ^ t <= C) :
    |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t p' q| <= C := by
  have hcard := natCard_stoppedCouplingBadAt_le_endpointFailures
    R t p p' q level hmirror
  have hcardReal :
      (Nat.card
          (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) :
        Real) <=
      ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingSourceFailureAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
            R t p p' q level) : Nat) : Real) := by
    exact_mod_cast hcard
  calc
    _ <= (Nat.card
        (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) :
          Real) / (4 : Real) ^ t :=
      isingLeapfrogStoppedKernel_reflectionCoupling_abs_le_badAt
        R t p p' q level
    _ <= ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingSourceFailureAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
            R t p p' q level) : Nat) : Real) / (4 : Real) ^ t :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ <= C := hfail


theorem isingLeapfrogExitKernel_reflectedStart_abs_le_of_endpointFailures
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (C : Real)
    (hfail :
      ((Nat.card (IsingLeapfrogChoiceNoHitAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingSourceFailureAtFamily
            R t p p' q level) +
          Nat.card (IsingStoppedCouplingMirrorFailureAtFamily
            R t p p' q level) : Nat) : Real) / (4 : Real) ^ t <= C) :
    |isingLeapfrogExitKernel R t p q -
        isingLeapfrogExitKernel R t p' q| <= C := by
  by_cases hq : isingLeapfrogBoxBoundary R q
  · simpa [isingLeapfrogExitKernel, hq] using
      isingLeapfrogStoppedKernel_reflectedStart_abs_le_of_endpointFailures
        R t p p' q level hmirror C hfail
  · have hC : 0 <= C := by
      exact le_trans (by positivity) hfail
    simp [isingLeapfrogExitKernel, hq, hC]

end StatMech.Universality
