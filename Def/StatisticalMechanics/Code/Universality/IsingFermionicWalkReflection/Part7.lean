/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part5


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

def FirstHitFamily (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :=
  {w : IsingDiagonalWalkHitSplit start level //
    w.FirstHit ∧ w.Valid ∧ w.steps.length = walkLength ∧ w.endpoint = target}

def reflectFirstHitFamily
    {start : Int × Int} {level : Int} {walkLength : Nat}
    {target : Int × Int} :
    FirstHitFamily start level walkLength target →
      FirstHitFamily start level walkLength (reflectedEndpoint level target) :=
  fun w ↦ ⟨w.1.reflect, reflect_firstHit w.1 w.2.1,
    reflect_valid w.1 w.2.2.1, by
      rw [reflect_length]
      exact w.2.2.2.1, by
      apply Prod.ext
      · rw [reflect_endpoint_fst, w.2.2.2.2]
        rfl
      · rw [reflect_endpoint_snd, w.2.2.2.2]
        rfl⟩

def reflectFirstHitFamilyBack
    {start : Int × Int} {level : Int} {walkLength : Nat}
    {target : Int × Int} :
    FirstHitFamily start level walkLength (reflectedEndpoint level target) →
      FirstHitFamily start level walkLength target :=
  fun w ↦ ⟨w.1.reflect, reflect_firstHit w.1 w.2.1,
    reflect_valid w.1 w.2.2.1, by
      rw [reflect_length]
      exact w.2.2.2.1, by
      apply Prod.ext
      · rw [reflect_endpoint_fst, w.2.2.2.2]
        unfold reflectedEndpoint
        dsimp
        omega
      · rw [reflect_endpoint_snd, w.2.2.2.2]
        rfl⟩


def reflectFirstHitFamilyEquiv
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    FirstHitFamily start level walkLength target ≃
      FirstHitFamily start level walkLength (reflectedEndpoint level target) where
  toFun := reflectFirstHitFamily
  invFun := reflectFirstHitFamilyBack
  left_inv w := by
    apply Subtype.ext
    simp [reflectFirstHitFamily, reflectFirstHitFamilyBack]
  right_inv w := by
    apply Subtype.ext
    simp [reflectFirstHitFamily, reflectFirstHitFamilyBack]

end IsingDiagonalWalkHitSplit
end StatMech.Universality
