/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCheckerboard.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareRadialPatchPrimalDirichlet
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) : FKIsingSquareRadialPatchPrimalNode m → Real := by
  letI : Nonempty (FKIsingSquareRadialPatchPrimalNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨0, hmpos⟩), by simp⟩⟩
  exact Classical.choose (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalGraph_reachable_boundary n m hm)
    (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base))

end
end StatMech.Universality
