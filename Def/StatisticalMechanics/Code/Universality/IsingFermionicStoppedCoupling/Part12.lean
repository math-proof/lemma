/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part9


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def lineBoundaryStringEquivSum (m K : Nat) (hm : 0 < m) :
    IsingLineBoundaryStringFamily m K ≃
      IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ where
  toFun := lineBoundaryStringToSum m K hm
  invFun := lineBoundarySumToString m K
  left_inv := lineBoundaryString_leftInverse m K hm
  right_inv := lineBoundaryString_rightInverse m K hm

end
end StatMech.Universality
