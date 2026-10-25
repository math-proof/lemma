/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem horizontalChoiceSteps_length (bs : List Bool) :
    (horizontalChoiceSteps bs).length = bs.length := by
  simp [horizontalChoiceSteps]

theorem horizontalChoiceSteps_valid (bs : List Bool) :
    IsingDiagonalWalkStepsValid (horizontalChoiceSteps bs) := by
  intro d hd
  simp only [horizontalChoiceSteps, List.mem_map] at hd
  rcases hd with ⟨b, hb, rfl⟩
  cases b <;> simp [horizontalChoiceStep]

theorem horizontalChoiceSteps_vertical (bs : List Bool) :
    ∀ d ∈ horizontalChoiceSteps bs, d.2 = 1 := by
  intro d hd
  simp only [horizontalChoiceSteps, List.mem_map] at hd
  rcases hd with ⟨b, hb, rfl⟩
  simp [horizontalChoiceStep]

theorem horizontalStepCode_choiceStep (b : Bool) :
    horizontalStepCode (horizontalChoiceStep b) = b := by
  cases b <;> simp [horizontalStepCode, horizontalChoiceStep]

theorem horizontalStepCodes_choiceSteps (bs : List Bool) :
    (horizontalChoiceSteps bs).map horizontalStepCode = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change horizontalStepCode (horizontalChoiceStep b) ::
        (horizontalChoiceSteps bs).map horizontalStepCode = b :: bs
      rw [horizontalStepCode_choiceStep, ih]

theorem horizontalChoiceSteps_stepCodes_of_valid
    (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path)
    (hvertical : ∀ d ∈ path, d.2 = 1) :
    horizontalChoiceSteps (path.map horizontalStepCode) = path := by
  induction path with
  | nil => rfl
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have hdvertical := hvertical d (by simp)
      have htailValid : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have htailVertical : ∀ e ∈ path, e.2 = 1 := by
        intro e he
        exact hvertical e (by simp [he])
      have hstep : horizontalChoiceStep (horizontalStepCode d) = d := by
        rcases hd.1 with hdx | hdx <;>
          apply Prod.ext <;>
          simp [horizontalChoiceStep, horizontalStepCode, hdx, hdvertical]
      change horizontalChoiceStep (horizontalStepCode d) ::
        horizontalChoiceSteps (path.map horizontalStepCode) = d :: path
      rw [hstep, ih htailValid htailVertical]

theorem lineFreeEndpoint_horizontalChoiceSteps
    (bs : List Bool) (start : Int) :
    lineFreeEndpoint start bs =
      (isingDiagonalWalkEndpoint (start, 0)
        (horizontalChoiceSteps bs)).1 := by
  induction bs generalizing start with
  | nil =>
      simp [lineFreeEndpoint, horizontalChoiceSteps,
        isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      cases b with
      | false =>
          convert ih (start - 1) using 1 <;>
            simp [lineFreeEndpoint, horizontalChoiceSteps,
            horizontalChoiceStep, isingDiagonalWalkEndpoint,
            isingDiagonalWalkNext, isingDiagonalWalkDisplacement, add_assoc] <;>
            ring
      | true =>
          convert ih (start + 1) using 1 <;>
            simp [lineFreeEndpoint, horizontalChoiceSteps,
            horizontalChoiceStep, isingDiagonalWalkEndpoint,
            isingDiagonalWalkNext, isingDiagonalWalkDisplacement, add_assoc] <;>
            ring

theorem lineFreeEndpoint_add (bs : List Bool) (start shift : Int) :
    lineFreeEndpoint (start + shift) bs =
      lineFreeEndpoint start bs + shift := by
  induction bs generalizing start with
  | nil => simp [lineFreeEndpoint]
  | cons b bs ih =>
      rw [lineFreeEndpoint, lineFreeEndpoint]
      calc
        lineFreeEndpoint (start + shift + (if b then 1 else -1)) bs =
            lineFreeEndpoint ((start + (if b then 1 else -1)) + shift) bs := by
              congr 1
              ring
        _ = lineFreeEndpoint (start + (if b then 1 else -1)) bs + shift :=
          ih (start + (if b then 1 else -1))


end
end StatMech.Universality
