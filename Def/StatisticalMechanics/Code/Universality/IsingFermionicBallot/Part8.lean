/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def horizontalFirstHitBelowLowerToUpper
    (t : Nat) (level : Int) :
    HorizontalFirstHitBelow t (level - 1) level →
      HorizontalFirstHitBelow t (level + 1) level := fun w => by
  simpa only [show 2 * level - (level - 1) = level + 1 by ring] using
    horizontalFirstHitBelowReflect t (level - 1) level w

def horizontalFirstHitBelowUpperToLower
    (t : Nat) (level : Int) :
    HorizontalFirstHitBelow t (level + 1) level →
      HorizontalFirstHitBelow t (level - 1) level := fun w => by
  simpa only [show 2 * level - (level + 1) = level - 1 by ring] using
    horizontalFirstHitBelowReflect t (level + 1) level w

end
end StatMech.Universality
