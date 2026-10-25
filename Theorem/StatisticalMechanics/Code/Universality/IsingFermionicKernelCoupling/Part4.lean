/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem isingLeapfrogChoiceSteps_valid (bs : List (Bool × Bool)) :
    IsingDiagonalWalkStepsValid (isingLeapfrogChoiceSteps bs) := by
  intro d hd
  simp only [isingLeapfrogChoiceSteps, List.mem_map] at hd
  rcases hd with ⟨b, hb, rfl⟩
  cases b with
  | mk bx byy =>
      cases bx <;> cases byy <;> simp [isingLeapfrogChoiceStep]

theorem isingLeapfrogBoxInt_choiceNext
    (R : Nat) (p : IsingLeapfrogBox R) (b : Bool × Bool)
    (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxInt (isingLeapfrogChoiceNext R p b) =
      isingDiagonalWalkNext (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceStep b) := by
  rcases b with ⟨bx, byy⟩
  cases bx <;> cases byy <;>
    simp only [isingLeapfrogChoiceNext, hp, ↓reduceDIte]
  all_goals
    apply Prod.ext <;>
      simp [isingLeapfrogBoxInt, isingLeapfrogChoiceStep,
        isingDiagonalWalkNext, isingLeapfrogSW, isingLeapfrogSE,
        isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogWest,
        isingLeapfrogEast, isingLeapfrogSouth, isingLeapfrogNorth] <;>
      unfold isingLeapfrogBoxBoundary at hp <;> omega

theorem IsingLeapfrogKilledChoiceValid.run_boxInt_eq_endpoint
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogKilledChoiceValid R p bs) :
    isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p bs) =
      isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
        (isingLeapfrogChoiceSteps bs) := by
  induction bs generalizing p with
  | nil =>
      simp [isingLeapfrogChoiceRun, isingLeapfrogChoiceSteps,
        isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      rw [show isingLeapfrogChoiceRun R p (b :: bs) =
          isingLeapfrogChoiceRun R (isingLeapfrogChoiceNext R p b) bs by
        rfl]
      rw [ih (isingLeapfrogChoiceNext R p b) h.2]
      rw [isingLeapfrogBoxInt_choiceNext R p b h.1]
      unfold isingLeapfrogChoiceSteps isingDiagonalWalkEndpoint
        isingDiagonalWalkNext isingDiagonalWalkDisplacement
      apply Prod.ext <;> simp <;> ring

theorem IsingLeapfrogKilledChoiceValid.take
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogKilledChoiceValid R p bs) (k : Nat) :
    IsingLeapfrogKilledChoiceValid R p (bs.take k) := by
  induction bs generalizing p k with
  | nil => simpa using h
  | cons b bs ih =>
      cases k with
      | zero => exact h.1
      | succ k =>
          exact ⟨h.1, ih (isingLeapfrogChoiceNext R p b) h.2 k⟩

theorem isingLeapfrogBoxInt_inOpenBox_iff
    (R : Nat) (p : IsingLeapfrogBox R) :
    InOpenBox R (isingLeapfrogBoxInt p) ↔
      ¬ isingLeapfrogBoxBoundary R p := by
  unfold InOpenBox isingLeapfrogBoxInt isingLeapfrogBoxBoundary
  simp only [Prod.fst, Prod.snd]
  constructor
  · intro h
    omega
  · intro h
    have hx := p.1.2
    have hy := p.2.2
    push_cast
    omega

theorem IsingLeapfrogKilledChoiceValid.staysInOpenBox
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogKilledChoiceValid R p bs) :
    StaysInOpenBox R (isingLeapfrogBoxInt p)
      (isingLeapfrogChoiceSteps bs) := by
  intro k hk
  have htake := h.take R p bs k
  have hrun := htake.run_boxInt_eq_endpoint R p (bs.take k)
  have hopen : InOpenBox R
      (isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p (bs.take k))) :=
    (isingLeapfrogBoxInt_inOpenBox_iff R _).2
      (htake.endpoint_not_boundary R p (bs.take k))
  rw [hrun] at hopen
  simpa [isingLeapfrogChoiceSteps, List.map_take] using hopen

end
end StatMech.Universality
