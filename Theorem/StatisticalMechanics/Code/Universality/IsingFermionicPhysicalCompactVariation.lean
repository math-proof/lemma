/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteBoundaryCutoff.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCaccioppoli.Part2


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

theorem fkIsingSquareRadialPatchPrimalBoundary_nonempty
    (m : Nat) (hm : 0 < m) :
    ∃ p : FKIsingSquareRadialPatchPrimalNode m,
      fkIsingSquareRadialPatchPrimalBoundary m p := by
  let p : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨0, hm⟩, ⟨0, hm⟩), by norm_num⟩
  exact ⟨p, by simp [p, fkIsingSquareRadialPatchPrimalBoundary]⟩

theorem fkIsingSquareRadialPatchDualBoundary_nonempty
    (m : Nat) (hm : 2 ≤ m) :
    ∃ p : FKIsingSquareRadialPatchDualNode m,
      fkIsingSquareRadialPatchDualBoundary m p := by
  let p : FKIsingSquareRadialPatchDualNode m :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by norm_num⟩
  exact ⟨p, by simp [p, fkIsingSquareRadialPatchDualBoundary]⟩

end
end StatMech.Universality
