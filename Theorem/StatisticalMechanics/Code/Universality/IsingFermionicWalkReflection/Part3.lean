/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part4


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

@[simp] theorem reflect_before (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.before = w.before := rfl

@[simp] theorem reflect_after (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.after = w.after.map reflectIncrement := rfl

@[simp] theorem reflect_reflect (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.reflect = w := by
  cases w with
  | mk before after hit =>
      simp [reflect, reflectIncrement, Function.comp_def]


end IsingDiagonalWalkHitSplit
end StatMech.Universality
