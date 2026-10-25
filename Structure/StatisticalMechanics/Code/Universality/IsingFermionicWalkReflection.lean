/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection


namespace StatMech.Universality

structure IsingDiagonalWalkHitSplit (start : Int × Int) (level : Int) where
  before : List (Int × Int)
  after : List (Int × Int)
  hit : start.1 + (isingDiagonalWalkDisplacement before).1 = level

end StatMech.Universality
