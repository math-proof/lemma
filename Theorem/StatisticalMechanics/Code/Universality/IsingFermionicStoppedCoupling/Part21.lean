/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part25


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem mirrorFailureToSource_injective
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    Function.Injective (mirrorFailureToSource R t p p' level hmirror) := by
  intro a b h
  apply Subtype.ext
  apply (isingLeapfrogCouplingChoiceEquiv t (isingLeapfrogBoxInt p) level).injective
  exact congrArg (fun z => z.1) h

end
end StatMech.Universality
