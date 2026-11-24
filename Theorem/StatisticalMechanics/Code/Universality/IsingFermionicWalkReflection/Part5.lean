module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

@[simp] theorem reflectedEndpoint_reflectedEndpoint (level : Int)
    (target : Int × Int) :
    reflectedEndpoint level (reflectedEndpoint level target) = target := by
  unfold reflectedEndpoint
  ext <;> simp


end IsingDiagonalWalkHitSplit
end StatMech.Universality
