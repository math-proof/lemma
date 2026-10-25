/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem flipXChoices_involutive : Function.Involutive isingLeapfrogFlipXChoices := by
  intro bs
  unfold isingLeapfrogFlipXChoices
  simp [Function.comp_def]

theorem flipXChoices_injective : Function.Injective isingLeapfrogFlipXChoices :=
  flipXChoices_involutive.injective

theorem boxReflectX_choiceNext
    (R : Nat) (p : IsingLeapfrogBox R) (b : Bool × Bool) :
    isingLeapfrogBoxReflectX R (isingLeapfrogChoiceNext R p b) =
      isingLeapfrogChoiceNext R (isingLeapfrogBoxReflectX R p) (!b.1, b.2) := by
  by_cases hp : isingLeapfrogBoxBoundary R p
  · have hpr := (isingLeapfrogBoxBoundary_reflectX_iff R p).2 hp
    simp [isingLeapfrogChoiceNext, hp, hpr]
  · have hpr : ¬ isingLeapfrogBoxBoundary R (isingLeapfrogBoxReflectX R p) :=
      mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp
    rcases b with ⟨bx, byy⟩
    cases bx <;> cases byy <;>
      simp only [isingLeapfrogChoiceNext, hp, hpr, ↓reduceDIte,
        Bool.not_false, Bool.not_true]
    all_goals
      apply Prod.ext <;> apply Fin.ext <;>
        simp [isingLeapfrogBoxReflectX, isingLeapfrogSW, isingLeapfrogSE,
          isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogWest,
          isingLeapfrogEast, isingLeapfrogSouth, isingLeapfrogNorth] <;>
        unfold isingLeapfrogBoxBoundary at hp <;> omega

theorem choiceRun_reflectX
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool)) :
    isingLeapfrogChoiceRun R (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogFlipXChoices bs) =
      isingLeapfrogBoxReflectX R (isingLeapfrogChoiceRun R p bs) := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLeapfrogFlipXChoices, List.map_cons,
        isingLeapfrogChoiceRun]
      rw [← boxReflectX_choiceNext]
      exact ih (isingLeapfrogChoiceNext R p b)

theorem choiceExecValid_reflectX_iff
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool)) :
    IsingLeapfrogChoiceExecValid R (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogFlipXChoices bs) ↔
      IsingLeapfrogChoiceExecValid R p bs := by
  constructor
  · intro h j hj
    have hj' : j < (isingLeapfrogFlipXChoices bs).length := by simpa [isingLeapfrogFlipXChoices] using hj
    have h' := h j hj'
    have htake : (isingLeapfrogFlipXChoices bs).take j =
        isingLeapfrogFlipXChoices (bs.take j) := by
      simp [isingLeapfrogFlipXChoices, List.map_take]
    rw [htake, choiceRun_reflectX] at h'
    exact mt (isingLeapfrogBoxBoundary_reflectX_iff R _).mpr h'
  · intro h j hj
    have h' := h j (by simpa [isingLeapfrogFlipXChoices] using hj)
    have htake : (isingLeapfrogFlipXChoices bs).take j =
        isingLeapfrogFlipXChoices (bs.take j) := by
      simp [isingLeapfrogFlipXChoices, List.map_take]
    rw [htake, choiceRun_reflectX]
    exact mt (isingLeapfrogBoxBoundary_reflectX_iff R _).mp h'

theorem choiceSteps_flipX
    (bs : List (Bool × Bool)) :
    isingLeapfrogChoiceSteps (isingLeapfrogFlipXChoices bs) =
      (isingLeapfrogChoiceSteps bs).map reflectIncrement := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rcases b with ⟨bx, byy⟩
      cases bx <;> cases byy <;>
        simp [isingLeapfrogFlipXChoices, isingLeapfrogChoiceSteps,
          isingLeapfrogChoiceStep, reflectIncrement, ih]

theorem displacement_map_reflectIncrement (path : List (Int × Int)) :
    isingDiagonalWalkDisplacement (path.map reflectIncrement) =
      (-(isingDiagonalWalkDisplacement path).1,
        (isingDiagonalWalkDisplacement path).2) := by
  have hneg : (path.map (fun d => -d.1)).sum =
      -(path.map Prod.fst).sum := by
    induction path with
    | nil => simp
    | cons d path ih => simp [ih, add_comm]
  unfold isingDiagonalWalkDisplacement
  apply Prod.ext
  · simp only [List.map_map]
    change (path.map (fun d => -d.1)).sum = -(path.map Prod.fst).sum
    exact hneg
  · simp [Function.comp_def, reflectIncrement]

end
end StatMech.Universality
