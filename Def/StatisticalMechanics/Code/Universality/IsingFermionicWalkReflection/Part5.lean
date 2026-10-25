/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part3


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

def reflectEquiv : IsingDiagonalWalkHitSplit start level ≃
    IsingDiagonalWalkHitSplit start level where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_reflect
  right_inv := reflect_reflect

end IsingDiagonalWalkHitSplit
end StatMech.Universality
