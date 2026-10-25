/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part10


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}


def reflectPrefix (w : IsingDiagonalWalkHitSplit start level) :
    IsingDiagonalWalkHitSplit (reflectedEndpoint level start) level where
  before := w.before.map reflectIncrement
  after := w.after
  hit := by
    rw [displacement_reflectSuffix]
    unfold reflectedEndpoint
    have hw := w.hit
    dsimp at hw ⊢
    omega

end IsingDiagonalWalkHitSplit
end StatMech.Universality
