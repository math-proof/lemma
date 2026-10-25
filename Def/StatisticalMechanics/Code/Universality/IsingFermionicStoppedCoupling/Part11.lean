/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def lineBoundaryStringToSum (m K : Nat) (hm : 0 < m) :
    IsingLineBoundaryStringFamily m K →
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

def lineBoundarySumToString (m K : Nat) :
    IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ ⊕
        IsingLineChoicePathFamily (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ →
      IsingLineBoundaryStringFamily m K
  | Sum.inl w => ⟨w.1, w.2.1, by
      unfold isingLineBoxBoundary
      left
      simpa [w.2.2]⟩
  | Sum.inr w => ⟨w.1, w.2.1, by
      unfold isingLineBoxBoundary
      right
      simpa [w.2.2]⟩

end
end StatMech.Universality
