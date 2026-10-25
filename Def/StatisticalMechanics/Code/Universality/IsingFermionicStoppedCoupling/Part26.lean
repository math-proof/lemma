/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part21


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def mirrorFailureReflectX
    (R t level : Nat) (p p' : IsingLeapfrogBox R)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level ≤ R) :
    IsingStoppedCouplingMirrorFailureFamily R t p p' (level : Int) →
      IsingStoppedCouplingSourceFailureFamily R t
        (isingLeapfrogBoxReflectX R p') ((R - level : Nat) : Int) :=
  fun w => sourceFailureReflectX R t p' level hlevelR
    (mirrorFailureToSource R t p p' (level : Int) hmirror w)

end
end StatMech.Universality
