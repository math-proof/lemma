/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part14


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}


def SurvivalMatchedFirstHitFamily (R : Nat) (start : Int × Int)
    (level : Int) (walkLength : Nat) (target : Int × Int) :=
  {w : FirstHitFamily start level walkLength target //
    StaysInOpenBox R start w.1.steps ∧
      StaysInOpenBox R (reflectedEndpoint level start)
        w.1.reflectPrefix.steps}


def SurvivalMatchedMirrorFamily (R : Nat) (start : Int × Int)
    (level : Int) (walkLength : Nat) (target : Int × Int) :=
  {w : FirstHitFamily (reflectedEndpoint level start) level walkLength target //
    StaysInOpenBox R (reflectedEndpoint level start) w.1.steps ∧
      StaysInOpenBox R start (unreflectPrefix w.1).steps}


def survivalMatchedFirstHitFamilyEquiv
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    SurvivalMatchedFirstHitFamily R start level walkLength target ≃
      SurvivalMatchedMirrorFamily R start level walkLength target where
  toFun w := ⟨reflectPrefixFirstHitFamily w.1, w.2.2, by
    simpa [reflectPrefixFirstHitFamily, unreflectPrefixFirstHitFamily] using
      w.2.1⟩
  invFun w := ⟨unreflectPrefixFirstHitFamily w.1, w.2.2, by
    simpa [reflectPrefixFirstHitFamily, unreflectPrefixFirstHitFamily] using
      w.2.1⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact unreflectPrefix_reflectPrefix w.1.1
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact reflectPrefix_unreflectPrefix w.1.1

end IsingDiagonalWalkHitSplit
end StatMech.Universality
