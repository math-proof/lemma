/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part13


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}


@[simp] theorem unreflectPrefix_reflectPrefix
    (w : IsingDiagonalWalkHitSplit start level) :
    unreflectPrefix w.reflectPrefix = w := by
  cases w with
  | mk before after hit =>
      simp [unreflectPrefix, reflectPrefix, reflectIncrement,
        Function.comp_def]

@[simp] theorem reflectPrefix_unreflectPrefix
    (w : IsingDiagonalWalkHitSplit (reflectedEndpoint level start) level) :
    (unreflectPrefix w).reflectPrefix = w := by
  cases w with
  | mk before after hit =>
      simp [unreflectPrefix, reflectPrefix, reflectIncrement,
        Function.comp_def]

end IsingDiagonalWalkHitSplit
end StatMech.Universality
