/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part15


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}


def SurvivingFirstHitFamily (R : Nat) (start : Int × Int)
    (level : Int) (walkLength : Nat) (target : Int × Int) :=
  {w : FirstHitFamily start level walkLength target //
    StaysInOpenBox R start w.1.steps}


def SurvivalExceptionalFirstHitFamily (R : Nat) (start : Int × Int)
    (level : Int) (walkLength : Nat) (target : Int × Int) :=
  {w : SurvivingFirstHitFamily R start level walkLength target //
    ¬ StaysInOpenBox R (reflectedEndpoint level start)
      w.1.1.reflectPrefix.steps}


def SurvivalExceptionalMirrorFamily (R : Nat) (start : Int × Int)
    (level : Int) (walkLength : Nat) (target : Int × Int) :=
  {w : SurvivingFirstHitFamily R (reflectedEndpoint level start) level
      walkLength target //
    ¬ StaysInOpenBox R start (unreflectPrefix w.1.1).steps}


noncomputable def survivingFirstHitFamilyPartitionEquiv
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    SurvivingFirstHitFamily R start level walkLength target ≃
      SurvivalMatchedFirstHitFamily R start level walkLength target ⊕
        SurvivalExceptionalFirstHitFamily R start level walkLength target where
  toFun w := by
    classical
    exact if h : StaysInOpenBox R (reflectedEndpoint level start)
        w.1.1.reflectPrefix.steps then
        Sum.inl ⟨w.1, w.2, h⟩
      else Sum.inr ⟨w, h⟩
  invFun
    | Sum.inl w => ⟨w.1, w.2.1⟩
    | Sum.inr w => w.1
  left_inv w := by
    classical
    dsimp
    split_ifs <;> apply Subtype.ext <;> rfl
  right_inv w := by
    classical
    rcases w with w | w
    · simp only
      rw [dif_pos w.2.2]
      congr 1
    · simp only
      rw [dif_neg w.2]
      congr 1


noncomputable def survivingMirrorFamilyPartitionEquiv
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    SurvivingFirstHitFamily R (reflectedEndpoint level start) level
        walkLength target ≃
      SurvivalMatchedMirrorFamily R start level walkLength target ⊕
        SurvivalExceptionalMirrorFamily R start level walkLength target where
  toFun w := by
    classical
    exact if h : StaysInOpenBox R start (unreflectPrefix w.1.1).steps then
        Sum.inl ⟨w.1, w.2, h⟩
      else Sum.inr ⟨w, h⟩
  invFun
    | Sum.inl w => ⟨w.1, w.2.1⟩
    | Sum.inr w => w.1
  left_inv w := by
    classical
    dsimp
    split_ifs <;> apply Subtype.ext <;> rfl
  right_inv w := by
    classical
    rcases w with w | w
    · simp only
      rw [dif_pos w.2.2]
      congr 1
    · simp only
      rw [dif_neg w.2]
      congr 1

end IsingDiagonalWalkHitSplit
end StatMech.Universality
