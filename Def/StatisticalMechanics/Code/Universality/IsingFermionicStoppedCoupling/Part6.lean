/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def choiceNoHitAllProjection
    (t : Nat) (start level : Int) :
    IsingLeapfrogChoiceNoHitAll t start level →
      IsingHorizontalNoHitFamily t start level ×
        {ys : List Bool // ys.length = t} := fun w =>
  ⟨⟨w.1.1.map Prod.fst, by simpa using w.1.2, by
      intro k hk
      simpa [List.map_take] using w.2 k hk⟩,
    ⟨w.1.1.map Prod.snd, by simpa using w.1.2⟩⟩

end
end StatMech.Universality
