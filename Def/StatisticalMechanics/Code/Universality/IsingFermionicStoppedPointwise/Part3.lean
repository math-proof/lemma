/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part2


namespace StatMech.Universality

open IsingDiagonalWalkHitSplit

noncomputable def stoppedCouplingBadAtCover
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level ->
      Sum (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level)
        (Sum
          (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level)
          (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level)) :=
  fun w => by
    classical
    let wb : IsingLeapfrogStoppedCouplingBadFamily R t p p' level :=
      ⟨w.1, w.2.1⟩
    by_cases hn : forall k, k <= t ->
        lineFreeEndpoint (isingLeapfrogBoxInt p).1
          ((w.1.1.map Prod.fst).take k) ≠ level
    · exact Sum.inl ⟨w.1, hn, w.2.2⟩
    · by_cases hs : IsingStoppedCouplingSourceFailure R p level w.1
      · exact Sum.inr (Sum.inl ⟨w.1, hs, w.2.2⟩)
      · exact Sum.inr (Sum.inr ⟨w.1, by
          exact (stoppedCouplingBad_cases R t p p' level hmirror wb)
            |>.resolve_left hn |>.resolve_left hs, w.2.2⟩)

def stoppedCouplingBadAtCoverValue
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Sum (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level)
        (Sum
          (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level)
          (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level)) ->
      IsingLeapfrogChoiceStringFamily t :=
  Sum.elim (fun w => w.1)
    (Sum.elim (fun w => w.1) (fun w => w.1))

end StatMech.Universality
