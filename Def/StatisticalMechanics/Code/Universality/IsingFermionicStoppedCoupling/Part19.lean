/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part14


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def stoppedCouplingBadCover
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    IsingLeapfrogStoppedCouplingBadFamily R t p p' level →
      IsingLeapfrogChoiceNoHitAll t (isingLeapfrogBoxInt p).1 level ⊕
        IsingStoppedCouplingSourceFailureFamily R t p level ⊕
          IsingStoppedCouplingMirrorFailureFamily R t p p' level := fun w => by
  classical
  by_cases hn : ∀ k, k ≤ t →
      lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.1.map Prod.fst).take k) ≠ level
  · exact Sum.inl ⟨w.1, by
      simpa [List.map_take] using hn⟩
  · by_cases hs : IsingStoppedCouplingSourceFailure R p level w.1
    · exact Sum.inr (Sum.inl ⟨w.1, hs⟩)
    · exact Sum.inr (Sum.inr ⟨w.1,
        (stoppedCouplingBad_cases R t p p' level hmirror w).resolve_left hn
          |>.resolve_left hs⟩)

def stoppedCouplingBadCoverValue
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogChoiceNoHitAll t (isingLeapfrogBoxInt p).1 level ⊕
        IsingStoppedCouplingSourceFailureFamily R t p level ⊕
          IsingStoppedCouplingMirrorFailureFamily R t p p' level →
      IsingLeapfrogChoiceStringFamily t :=
  Sum.elim (fun w => w.1) (Sum.elim (fun w => w.1) (fun w => w.1))

end
end StatMech.Universality
