/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part6


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem choiceStep_encodeStep_of_valid (d : Int × Int)
    (hd : (d.1 = 1 ∨ d.1 = -1) ∧ (d.2 = 1 ∨ d.2 = -1)) :
    isingLeapfrogChoiceStep (isingLeapfrogEncodeStep d) = d := by
  rcases hd with ⟨hdx | hdx, hdy | hdy⟩ <;>
    apply Prod.ext <;>
    simp [isingLeapfrogChoiceStep, isingLeapfrogEncodeStep, hdx, hdy]

theorem choiceSteps_encodeSteps_of_valid (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path) :
    isingLeapfrogChoiceSteps (isingLeapfrogEncodeSteps path) = path := by
  induction path with
  | nil => rfl
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have htail : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      change isingLeapfrogChoiceStep (isingLeapfrogEncodeStep d) ::
          isingLeapfrogChoiceSteps (isingLeapfrogEncodeSteps path) = d :: path
      rw [choiceStep_encodeStep_of_valid d hd, ih htail]

theorem killedChoiceValid_encodeSteps_of_stays
    (R : Nat) (p : IsingLeapfrogBox R) (path : List (Int × Int))
    (hvalid : IsingDiagonalWalkStepsValid path)
    (hstays : StaysInOpenBox R (isingLeapfrogBoxInt p) path) :
    IsingLeapfrogKilledChoiceValid R p
      (isingLeapfrogEncodeSteps path) := by
  induction path generalizing p with
  | nil =>
      have h0 := hstays 0 (by simp)
      simpa [isingLeapfrogEncodeSteps] using
        (isingLeapfrogBoxInt_inOpenBox_iff R p).1 (by
          simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
            using h0)
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have htailValid : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have h0 := hstays 0 (by simp)
      have hp : ¬ isingLeapfrogBoxBoundary R p :=
        (isingLeapfrogBoxInt_inOpenBox_iff R p).1 (by
          simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
            using h0)
      let b := isingLeapfrogEncodeStep d
      have hstep := isingLeapfrogBoxInt_choiceNext R p b hp
      rw [choiceStep_encodeStep_of_valid d hd] at hstep
      have htailStays : StaysInOpenBox R
          (isingLeapfrogBoxInt (isingLeapfrogChoiceNext R p b)) path := by
        intro k hk
        have horig := hstays (k + 1) (by simp; omega)
        rw [show (d :: path).take (k + 1) = d :: path.take k by
          simp [List.take_succ_cons]] at horig
        rw [hstep]
        have hend : isingDiagonalWalkEndpoint
            (isingDiagonalWalkNext (isingLeapfrogBoxInt p) d)
              (path.take k) =
            isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p)
              (d :: path.take k) := by
          unfold isingDiagonalWalkEndpoint isingDiagonalWalkNext
            isingDiagonalWalkDisplacement
          apply Prod.ext <;> simp <;> ring
        rw [hend]
        exact horig
      have htail := ih (isingLeapfrogChoiceNext R p b) htailValid htailStays
      exact ⟨hp, by simpa [isingLeapfrogEncodeSteps, b] using htail⟩

theorem isingLeapfrogBoxInt_injective {R : Nat} :
    Function.Injective (@isingLeapfrogBoxInt R) := by
  intro p q h
  unfold isingLeapfrogBoxInt at h
  apply Prod.ext <;> apply Fin.ext
  · exact Int.ofNat_inj.mp (congrArg Prod.fst h)
  · exact Int.ofNat_inj.mp (congrArg Prod.snd h)

theorem encodeStep_choiceStep (b : Bool × Bool) :
    isingLeapfrogEncodeStep (isingLeapfrogChoiceStep b) = b := by
  rcases b with ⟨bx, byy⟩
  cases bx <;> cases byy <;>
    simp [isingLeapfrogEncodeStep, isingLeapfrogChoiceStep]

theorem encodeSteps_choiceSteps (bs : List (Bool × Bool)) :
    isingLeapfrogEncodeSteps (isingLeapfrogChoiceSteps bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change isingLeapfrogEncodeStep (isingLeapfrogChoiceStep b) ::
          isingLeapfrogEncodeSteps (isingLeapfrogChoiceSteps bs) = b :: bs
      rw [encodeStep_choiceStep, ih]


end
end StatMech.Universality
