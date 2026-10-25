/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part9


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem stoppedCouplingBad_cases
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p))
    (w : IsingLeapfrogStoppedCouplingBadFamily R t p p' level) :
    (∀ k, k ≤ t →
      lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.1.map Prod.fst).take k) ≠ level) ∨
      IsingStoppedCouplingSourceFailure R p level w.1 ∨
        IsingStoppedCouplingMirrorFailure R p p' level w.1 := by
  classical
  cases hsplit : isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1.1) with
  | none =>
      left
      intro k hk heq
      have hne := firstHitSplit_none_endpoint_fst_ne hsplit k (by
        simpa [isingLeapfrogChoiceSteps, w.1.2] using hk)
      apply hne
      calc
        (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            ((isingLeapfrogChoiceSteps w.1.1).take k)).1 =
          (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
            (isingLeapfrogChoiceSteps (w.1.1.take k))).1 := by
              simp [isingLeapfrogChoiceSteps, List.map_take]
        _ = lineFreeEndpoint (isingLeapfrogBoxInt p).1
            ((w.1.1.map Prod.fst).take k) :=
          by simpa [List.map_take] using
            (lineFreeEndpoint_choiceHorizontal_full (w.1.1.take k)
              (isingLeapfrogBoxInt p)).symm
        _ = level := heq
  | some split =>
      right
      by_cases hs : IsingLeapfrogChoiceExecValid R p
        (w.1.1.take split.before.length)
      · by_cases hm : IsingLeapfrogChoiceExecValid R p'
          ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
            level w.1).1.take split.before.length)
        · exact (w.2 (stoppedCoupling_endpoints_eq_of_execValid_to_hit
            R t p p' level hmirror w.1 split hsplit hs hm)).elim
        · right
          exact ⟨split, hsplit, hm⟩
      · left
        exact ⟨split, hsplit, hs⟩

end
end StatMech.Universality
