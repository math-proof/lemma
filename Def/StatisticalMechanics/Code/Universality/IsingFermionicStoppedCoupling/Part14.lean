/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part11


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingLeapfrogHorizontalEscapeFamily (n t : Nat) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    isingLineChoiceRun n ⟨n - 1, by omega⟩ (w.1.map Prod.fst) =
      (⟨0, by omega⟩ : IsingLineBox n)}

end
end StatMech.Universality
