/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def killedChoicePathFamilyEmptyEquiv
    (R t : Nat) (p q : IsingLeapfrogBox R)
    (h : ∀ w : IsingLeapfrogKilledChoicePathFamily R t p q, False) :
    IsingLeapfrogKilledChoicePathFamily R t p q ≃ Empty where
  toFun w := (h w).elim
  invFun e := e.elim
  left_inv w := (h w).elim
  right_inv e := e.elim

def killedChoicePathFamilySuccEquiv (R t : Nat)
    (p q : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    IsingLeapfrogKilledChoicePathFamily R (t + 1) p q ≃
      Σ b : Bool × Bool,
        IsingLeapfrogKilledChoicePathFamily R t
          (isingLeapfrogChoiceNext R p b) q where
  toFun w := by
    rcases w with ⟨bs, hlen, hvalid, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
        exact ⟨b, ⟨bs, by simpa using hlen, hvalid.2, by
          simpa [isingLeapfrogChoiceRun] using hend⟩⟩
  invFun w := ⟨w.1 :: w.2.1, by simp [w.2.2.1],
    ⟨hp, w.2.2.2.1⟩, by
      simpa [isingLeapfrogChoiceRun] using w.2.2.2.2⟩
  left_inv w := by
    rcases w with ⟨bs, hlen, hvalid, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs => rfl
  right_inv w := by
    rcases w with ⟨b, bs, hlen, hvalid, hend⟩
    rfl

def killedChoicePathFamilyZeroSelfEquiv (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    IsingLeapfrogKilledChoicePathFamily R 0 p p ≃ ULift.{1, 0} Unit where
  toFun _ := ⟨Unit.unit⟩
  invFun _ := ⟨[], rfl, hp, rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact (List.eq_nil_of_length_eq_zero w.2.1).symm
  right_inv _ := rfl


end
end StatMech.Universality
