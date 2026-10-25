/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part7


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def horizontalFreeBelowUpperEquivDeepLower
    (t : Nat) (level : Int) :
    HorizontalFreeBelow t (level + 1) level ≃
      HorizontalFreeBelow t (level - 1) (level - 2) where
  toFun w := ⟨w.1, w.2.1, by
    have hshift := lineFreeEndpoint_add w.1 (level - 1) 2
    have hstart : level - 1 + 2 = level + 1 := by ring
    rw [hstart] at hshift
    have hu := w.2.2
    rw [hshift] at hu
    omega⟩
  invFun w := ⟨w.1, w.2.1, by
    have hshift := lineFreeEndpoint_add w.1 (level - 1) 2
    have hstart : level - 1 + 2 = level + 1 := by ring
    rw [hstart] at hshift
    have hd := w.2.2
    rw [hshift]
    omega⟩
  left_inv w := Subtype.ext rfl
  right_inv w := Subtype.ext rfl

end
end StatMech.Universality
