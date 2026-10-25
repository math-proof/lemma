/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part2


namespace StatMech.Universality

open Finset

noncomputable section

def isingLineChoicePathFamilySuccEquiv (n t : Nat)
    (p q : IsingLineBox n) :
    IsingLineChoicePathFamily n (t + 1) p q ≃
      Σ b : Bool, IsingLineChoicePathFamily n t
        (isingLineChoiceNext n p b) q where
  toFun w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
        exact ⟨b, ⟨bs, by simpa using hlen, by
          simpa [isingLineChoiceRun] using hend⟩⟩
  invFun w := ⟨w.1 :: w.2.1, by simp [w.2.2.1], by
    simpa [isingLineChoiceRun] using w.2.2.2⟩
  left_inv w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs => rfl
  right_inv w := by
    rcases w with ⟨b, bs, hlen, hend⟩
    rfl

def isingLineChoicePathFamilyZeroSelfEquiv (n : Nat)
    (p : IsingLineBox n) :
    IsingLineChoicePathFamily n 0 p p ≃ ULift.{1, 0} Unit where
  toFun _ := ⟨Unit.unit⟩
  invFun _ := ⟨[], rfl, rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact (List.eq_nil_of_length_eq_zero w.2.1).symm
  right_inv _ := rfl

def isingLineChoicePathFamilyZeroNeEquiv (n : Nat)
    (p q : IsingLineBox n) (hpq : p ≠ q) :
    IsingLineChoicePathFamily n 0 p q ≃ Empty where
  toFun w := by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    have : p = q := by simpa [hnil, isingLineChoiceRun] using w.2.2
    exact (hpq this).elim
  invFun e := e.elim
  left_inv w := (hpq (by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    simpa [hnil, isingLineChoiceRun] using w.2.2)).elim
  right_inv e := e.elim


end
end StatMech.Universality
