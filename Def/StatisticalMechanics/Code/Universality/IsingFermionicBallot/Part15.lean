/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part11


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def horizontalNoHitLowerUpperEquiv
    (t : Nat) (level : Int) :
    IsingHorizontalNoHitFamily t (level - 1) level ≃
      IsingHorizontalNoHitFamily t (level + 1) level where
  toFun w := ⟨w.1.map (!·), by simpa using w.2.1, by
    intro k hk heq
    have hreflect := lineFreeEndpoint_map_not (w.1.take k) (level - 1) level
    have htake : (w.1.map (!·)).take k = (w.1.take k).map (!·) := by
      simp [List.map_take]
    rw [htake] at heq
    have horig : lineFreeEndpoint (level - 1) (w.1.take k) = level := by
      rw [show 2 * level - (level - 1) = level + 1 by ring] at hreflect
      omega
    exact w.2.2 k hk horig⟩
  invFun w := ⟨w.1.map (!·), by simpa using w.2.1, by
    intro k hk heq
    have hreflect := lineFreeEndpoint_map_not (w.1.take k) (level + 1) level
    have htake : (w.1.map (!·)).take k = (w.1.take k).map (!·) := by
      simp [List.map_take]
    rw [htake] at heq
    have horig : lineFreeEndpoint (level + 1) (w.1.take k) = level := by
      rw [show 2 * level - (level + 1) = level - 1 by ring] at hreflect
      omega
    exact w.2.2 k hk horig⟩
  left_inv w := by
    apply Subtype.ext
    simpa [Function.comp_def] using List.map_map (!·) (!·) w.1
  right_inv w := by
    apply Subtype.ext
    simpa [Function.comp_def] using List.map_map (!·) (!·) w.1


end
end StatMech.Universality
