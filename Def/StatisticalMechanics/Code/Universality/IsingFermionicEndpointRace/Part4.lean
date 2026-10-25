/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace


namespace StatMech.Universality

open Finset

noncomputable section

def endpointBoundaryStringToSum (m K : Nat) (hm : 0 < m) :
    EndpointBoundaryStringFamily m K →
      IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ := fun w => by
  by_cases hzero : (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0
  · exact Sum.inl ⟨w.1, w.2.1, Fin.ext hzero⟩
  · exact Sum.inr ⟨w.1, w.2.1, Fin.ext (by
      have hb := w.2.2
      unfold isingLineBoxBoundary at hb
      rcases hb with h | h
      · exact (hzero h).elim
      · exact h)⟩

def endpointBoundarySumToString (m K : Nat) :
    IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ →
      EndpointBoundaryStringFamily m K
  | Sum.inl w => ⟨w.1, w.2.1, by
      unfold isingLineBoxBoundary
      left
      simpa [w.2.2]⟩
  | Sum.inr w => ⟨w.1, w.2.1, by
      unfold isingLineBoxBoundary
      right
      simpa [w.2.2]⟩

def endpointBoundaryStringEquivSum
    (m K : Nat) (hm : 0 < m) :
    EndpointBoundaryStringFamily m K ≃
      IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ where
  toFun := endpointBoundaryStringToSum m K hm
  invFun := endpointBoundarySumToString m K
  left_inv w := by
    unfold endpointBoundaryStringToSum
    by_cases hzero :
        (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0
    · rw [dif_pos hzero]
      rfl
    · rw [dif_neg hzero]
      rfl
  right_inv w := by
    cases w with
    | inl w =>
        unfold endpointBoundarySumToString endpointBoundaryStringToSum
        have hzero :
            (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 = 0 := by
          simp [w.2.2]
        rw [dif_pos hzero]
        apply congrArg Sum.inl
        exact Subtype.ext rfl
    | inr w =>
        unfold endpointBoundarySumToString endpointBoundaryStringToSum
        have hne :
            (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ w.1).1 ≠ 0 := by
          simp [w.2.2]
          omega
        rw [dif_neg hne]
        apply congrArg Sum.inr
        exact Subtype.ext rfl

end
end StatMech.Universality
