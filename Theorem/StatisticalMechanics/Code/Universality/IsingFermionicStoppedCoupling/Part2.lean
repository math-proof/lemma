/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem couplingReflectSteps_length
    (start : Int × Int) (level : Int) (path : List (Int × Int)) :
    (isingDiagonalWalkCouplingReflectSteps start level path).length =
      path.length := by
  unfold isingDiagonalWalkCouplingReflectSteps
  cases hsplit : isingDiagonalWalkFirstHitSplit? start level path with
  | none => simp
  | some split =>
      rw [reflectPrefix_length, firstHitSplit_steps hsplit]

theorem couplingReflectSteps_valid
    (start : Int × Int) (level : Int) (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path) :
    IsingDiagonalWalkStepsValid
      (isingDiagonalWalkCouplingReflectSteps start level path) := by
  unfold isingDiagonalWalkCouplingReflectSteps
  cases hsplit : isingDiagonalWalkFirstHitSplit? start level path with
  | none => exact reflectAll_valid path hvalid
  | some split =>
      apply reflectPrefix_valid
      unfold IsingDiagonalWalkHitSplit.Valid
      rw [firstHitSplit_steps hsplit]
      exact hvalid

theorem couplingReflectSteps_involutive
    (start : Int × Int) (level : Int) (path : List (Int × Int)) :
    isingDiagonalWalkCouplingReflectSteps (reflectedEndpoint level start) level
        (isingDiagonalWalkCouplingReflectSteps start level path) = path := by
  unfold isingDiagonalWalkCouplingReflectSteps
  cases hsplit : isingDiagonalWalkFirstHitSplit? start level path with
  | none =>
      rw [firstHitSplit_reflectAll_eq_none hsplit]
      simp [reflectIncrement, Function.comp_def]
  | some split =>
      have hreflect : isingDiagonalWalkFirstHitSplit?
          (reflectedEndpoint level start) level split.reflectPrefix.steps =
            some split.reflectPrefix :=
        firstHitSplit_eq_some split.reflectPrefix
          (reflectPrefix_firstHit split (firstHitSplit_firstHit hsplit))
      rw [hreflect]
      rw [← firstHitSplit_steps hsplit]
      simp [IsingDiagonalWalkHitSplit.steps, reflectPrefix, reflectIncrement,
        Function.comp_def]


end
end StatMech.Universality
