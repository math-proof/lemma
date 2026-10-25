/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part3


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

noncomputable instance firstHitFamily_finite
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (FirstHitFamily start level walkLength target) := by
  letI : Fintype
      {bits : List (Bool × Bool) // bits.length = walkLength} :=
    (List.finite_length_eq (Bool × Bool) walkLength).fintype
  exact Finite.of_injective firstHitFamilyCode firstHitFamilyCode_injective

noncomputable instance survivingFirstHitFamily_finite
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (SurvivingFirstHitFamily R start level walkLength target) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance survivalExceptionalFirstHitFamily_finite
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (SurvivalExceptionalFirstHitFamily R start level walkLength target) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance survivalExceptionalMirrorFamily_finite
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (SurvivalExceptionalMirrorFamily R start level walkLength target) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance survivalMatchedFirstHitFamily_finite
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (SurvivalMatchedFirstHitFamily R start level walkLength target) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance survivalMatchedMirrorFamily_finite
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Finite (SurvivalMatchedMirrorFamily R start level walkLength target) :=
  Finite.of_injective Subtype.val Subtype.val_injective


end IsingDiagonalWalkHitSplit
end StatMech.Universality
