/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def stoppedChoicePathFamilySuccEquiv (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    IsingLeapfrogStoppedChoicePathFamily R (t + 1) p q ≃
      Σ b : Bool × Bool,
        IsingLeapfrogStoppedChoicePathFamily R t
          (isingLeapfrogChoiceNext R p b) q where
  toFun w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
        exact ⟨b, ⟨bs, by simpa using hlen, by
          simpa [isingLeapfrogChoiceRun] using hend⟩⟩
  invFun w := ⟨w.1 :: w.2.1, by simp [w.2.2.1], by
    simpa [isingLeapfrogChoiceRun] using w.2.2.2⟩
  left_inv w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs => rfl
  right_inv w := by
    rcases w with ⟨b, bs, hlen, hend⟩
    rfl

def stoppedChoicePathFamilyZeroSelfEquiv (R : Nat)
    (p : IsingLeapfrogBox R) :
    IsingLeapfrogStoppedChoicePathFamily R 0 p p ≃ ULift.{1, 0} Unit where
  toFun _ := ⟨Unit.unit⟩
  invFun _ := ⟨[], rfl, rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact (List.eq_nil_of_length_eq_zero w.2.1).symm
  right_inv _ := rfl

def stoppedChoicePathFamilyZeroNeEquiv (R : Nat)
    (p q : IsingLeapfrogBox R) (hpq : p ≠ q) :
    IsingLeapfrogStoppedChoicePathFamily R 0 p q ≃ Empty where
  toFun w := by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    have : p = q := by simpa [hnil, isingLeapfrogChoiceRun] using w.2.2
    exact (hpq this).elim
  invFun e := e.elim
  left_inv w := (hpq (by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    simpa [hnil, isingLeapfrogChoiceRun] using w.2.2)).elim
  right_inv e := e.elim


end
end StatMech.Universality
