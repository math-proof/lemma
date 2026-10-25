/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def deepLowerEquivSubtype
    (t : Nat) (level : Int) :
    HorizontalFreeBelow t (level - 1) (level - 2) ≃
      {w : HorizontalFreeBelow t (level - 1) level //
        lineFreeEndpoint (level - 1) w.1 < level - 2} where
  toFun w := ⟨⟨w.1, w.2.1, by
    have h := w.2.2
    omega⟩, w.2.2⟩
  invFun w := ⟨w.1.1, w.1.2.1, w.2⟩
  left_inv w := Subtype.ext rfl
  right_inv w := Subtype.ext rfl

def centralBandEquivSubtype
    (t : Nat) (level : Int) :
    HorizontalCentralBand t level ≃
      {w : HorizontalFreeBelow t (level - 1) level //
        ¬ lineFreeEndpoint (level - 1) w.1 < level - 2} :=
  Equiv.refl _

end
end StatMech.Universality
