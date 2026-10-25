/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part12


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}


def reflectPrefixFirstHitFamily
    {walkLength : Nat} {target : Int × Int} :
    FirstHitFamily start level walkLength target →
      FirstHitFamily (reflectedEndpoint level start) level walkLength target :=
  fun w ↦ ⟨w.1.reflectPrefix, reflectPrefix_firstHit w.1 w.2.1,
    reflectPrefix_valid w.1 w.2.2.1, by
      rw [reflectPrefix_length]
      exact w.2.2.2.1, by
      rw [reflectPrefix_endpoint]
      exact w.2.2.2.2⟩

def unreflectPrefixFirstHitFamily
    {walkLength : Nat} {target : Int × Int} :
    FirstHitFamily (reflectedEndpoint level start) level walkLength target →
      FirstHitFamily start level walkLength target :=
  fun w ↦ ⟨unreflectPrefix w.1, by
      have h := reflectPrefix_firstHit w.1 w.2.1
      simpa [unreflectPrefix, reflectPrefix, FirstHit,
        reflectedEndpoint] using h, by
      have h := reflectPrefix_valid w.1 w.2.2.1
      simpa [unreflectPrefix, reflectPrefix, Valid, steps] using h, by
      simpa [unreflectPrefix, reflectPrefix, steps] using w.2.2.2.1, by
      have h := reflectPrefix_endpoint w.1
      simpa [unreflectPrefix, reflectPrefix, endpoint, steps,
        reflectedEndpoint] using h.trans w.2.2.2.2⟩


def reflectPrefixFirstHitFamilyEquiv
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    FirstHitFamily start level walkLength target ≃
      FirstHitFamily (reflectedEndpoint level start) level walkLength target where
  toFun := reflectPrefixFirstHitFamily
  invFun := unreflectPrefixFirstHitFamily
  left_inv w := by
    apply Subtype.ext
    exact unreflectPrefix_reflectPrefix w.1
  right_inv w := by
    apply Subtype.ext
    exact reflectPrefix_unreflectPrefix w.1

end IsingDiagonalWalkHitSplit
end StatMech.Universality
