/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part18


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def globalReflectHitSplit
    (R : Nat) {start : Int × Int} {level : Int}
    (split : IsingDiagonalWalkHitSplit start level) :
    IsingDiagonalWalkHitSplit ((R : Int) - start.1, start.2) ((R : Int) - level) where
  before := split.before.map reflectIncrement
  after := split.after.map reflectIncrement
  hit := by
    rw [displacement_map_reflectIncrement]
    have h := split.hit
    dsimp at h ⊢
    omega

end
end StatMech.Universality
