/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part9


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def horizontalCentralBandEquivEndpointSum
    (t : Nat) (level : Int) :
    HorizontalCentralBand t level ≃
      VerticalChoicePathFamily t (level - 1) (level - 2) ⊕
        VerticalChoicePathFamily t (level - 1) (level - 1) where
  toFun w := by
    by_cases hend : lineFreeEndpoint (level - 1) w.1.1 = level - 2
    · exact Sum.inl ⟨w.1.1, w.1.2.1, hend⟩
    · exact Sum.inr ⟨w.1.1, w.1.2.1, by
        have hlower := w.2
        have hupper := w.1.2.2
        omega⟩
  invFun w := w.elim
    (fun bs => ⟨⟨bs.1, bs.2.1, by rw [bs.2.2]; omega⟩, by
      rw [bs.2.2]
      omega⟩)
    (fun bs => ⟨⟨bs.1, bs.2.1, by rw [bs.2.2]; omega⟩, by
      rw [bs.2.2]
      omega⟩)
  left_inv w := by
    by_cases hend : lineFreeEndpoint (level - 1) w.1.1 = level - 2
    · simp [hend]
    · simp [hend]
  right_inv w := by
    rcases w with bs | bs
    · simp [bs.2.2]
    · have hne : lineFreeEndpoint (level - 1) bs.1 ≠ level - 2 := by
        rw [bs.2.2]
        omega
      simp [hne]

end
end StatMech.Universality
