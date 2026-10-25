/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def HorizontalFreeBelow (t : Nat) (start level : Int) :=
  {bs : List Bool // bs.length = t ∧ lineFreeEndpoint start bs < level}

end
end StatMech.Universality
