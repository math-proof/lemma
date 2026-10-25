/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part7


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def horizontalEscapeProjection (n t : Nat) :
    IsingLeapfrogHorizontalEscapeFamily n t →
      IsingLineChoicePathFamily n t ⟨n - 1, by omega⟩ ⟨0, by omega⟩ ×
        {ys : List Bool // ys.length = t} := fun w =>
  ⟨⟨w.1.1.map Prod.fst, by simpa using w.1.2, w.2⟩,
    ⟨w.1.1.map Prod.snd, by simpa using w.1.2⟩⟩

end
end StatMech.Universality
