/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem localHorizontalSteps_length (bs : List Bool) :
    (localHorizontalSteps bs).length = bs.length := by
  simp [localHorizontalSteps]

theorem localHorizontalSteps_valid (bs : List Bool) :
    IsingDiagonalWalkStepsValid (localHorizontalSteps bs) := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨b, hb, rfl⟩
  cases b <;> simp [localHorizontalStep]

theorem localHorizontalSteps_vertical (bs : List Bool) :
    ∀ d ∈ localHorizontalSteps bs, d.2 = 1 := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨b, hb, rfl⟩
  simp [localHorizontalStep]

theorem localHorizontalCode_step (b : Bool) :
    localHorizontalCode (localHorizontalStep b) = b := by
  cases b <;> simp [localHorizontalCode, localHorizontalStep]

theorem localHorizontalCodes_steps (bs : List Bool) :
    (localHorizontalSteps bs).map localHorizontalCode = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change localHorizontalCode (localHorizontalStep b) ::
        (localHorizontalSteps bs).map localHorizontalCode = b :: bs
      rw [localHorizontalCode_step, ih]

theorem localHorizontalSteps_codes
    (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path)
    (hvertical : ∀ d ∈ path, d.2 = 1) :
    localHorizontalSteps (path.map localHorizontalCode) = path := by
  induction path with
  | nil => rfl
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have hdv := hvertical d (by simp)
      have htail : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have htailv : ∀ e ∈ path, e.2 = 1 := by
        intro e he
        exact hvertical e (by simp [he])
      have hstep : localHorizontalStep (localHorizontalCode d) = d := by
        rcases hd.1 with hdx | hdx <;> apply Prod.ext <;>
          simp [localHorizontalStep, localHorizontalCode, hdx, hdv]
      change localHorizontalStep (localHorizontalCode d) ::
        localHorizontalSteps (path.map localHorizontalCode) = d :: path
      rw [hstep, ih htail htailv]

theorem lineFreeEndpoint_localHorizontalSteps
    (bs : List Bool) (start : Int) :
    lineFreeEndpoint start bs =
      (isingDiagonalWalkEndpoint (start, 0) (localHorizontalSteps bs)).1 := by
  induction bs generalizing start with
  | nil => simp [lineFreeEndpoint, localHorizontalSteps,
      isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      cases b with
      | false =>
          convert ih (start - 1) using 1 <;>
            simp [lineFreeEndpoint, localHorizontalSteps, localHorizontalStep,
              isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
              isingDiagonalWalkDisplacement, add_assoc] <;> ring
      | true =>
          convert ih (start + 1) using 1 <;>
            simp [lineFreeEndpoint, localHorizontalSteps, localHorizontalStep,
              isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
              isingDiagonalWalkDisplacement, add_assoc] <;> ring

end
end StatMech.Universality
