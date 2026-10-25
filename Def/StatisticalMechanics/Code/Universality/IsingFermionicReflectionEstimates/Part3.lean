/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

def verticalChoicePathFamilySuccEquiv (t : Nat) (x y : Int) :
    VerticalChoicePathFamily (t + 1) x y ≃
      Σ b : Bool, VerticalChoicePathFamily t
        (x + if b then 1 else -1) y where
  toFun w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
        exact ⟨b, ⟨bs, by simpa using hlen, by
          simpa [lineFreeEndpoint] using hend⟩⟩
  invFun w := ⟨w.1 :: w.2.1, by simp [w.2.2.1], by
    simpa [lineFreeEndpoint] using w.2.2.2⟩
  left_inv w := by
    rcases w with ⟨bs, hlen, hend⟩
    cases bs with
    | nil => simp at hlen
    | cons b bs => rfl
  right_inv w := by
    rcases w with ⟨b, bs, hlen, hend⟩
    rfl

def verticalChoicePathFamilyZeroSelfEquiv (x : Int) :
    VerticalChoicePathFamily 0 x x ≃ ULift.{1, 0} Unit where
  toFun _ := ⟨Unit.unit⟩
  invFun _ := ⟨[], rfl, rfl⟩
  left_inv w := by
    apply Subtype.ext
    exact (List.eq_nil_of_length_eq_zero w.2.1).symm
  right_inv _ := rfl

def verticalChoicePathFamilyZeroNeEquiv (x y : Int) (hxy : x ≠ y) :
    VerticalChoicePathFamily 0 x y ≃ Empty where
  toFun w := by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    have : x = y := by simpa [hnil, lineFreeEndpoint] using w.2.2
    exact (hxy this).elim
  invFun e := e.elim
  left_inv w := (hxy (by
    have hnil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
    simpa [hnil, lineFreeEndpoint] using w.2.2)).elim
  right_inv e := e.elim


end IsingDiagonalWalkHitSplit
end StatMech.Universality
