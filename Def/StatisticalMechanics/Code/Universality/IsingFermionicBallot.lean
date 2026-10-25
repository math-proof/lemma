/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def horizontalChoiceStep (b : Bool) : Int × Int :=
  (if b then 1 else -1, 1)

def horizontalChoiceSteps (bs : List Bool) : List (Int × Int) :=
  bs.map horizontalChoiceStep

def horizontalStepCode (d : Int × Int) : Bool :=
  decide (d.1 = 1)

end
end StatMech.Universality
