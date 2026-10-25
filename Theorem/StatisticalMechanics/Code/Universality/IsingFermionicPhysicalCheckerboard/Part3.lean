/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCheckerboard.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchPrimalDirichlet_harmonicOn
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    IsingFiniteGraphHarmonicOn
      (fkIsingSquareRadialPatchPrimalGraph n m hm)
      (fkIsingSquareRadialPatchPrimalBoundary m)
      (fkIsingSquareRadialPatchPrimalDirichlet n m hn hm hmpos base) := by
  letI : Nonempty (FKIsingSquareRadialPatchPrimalNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨0, hmpos⟩), by simp⟩⟩
  exact (Classical.choose_spec (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalGraph_reachable_boundary n m hm)
    (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base))).1

theorem fkIsingSquareRadialPatchPrimalDirichlet_boundary
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchPrimalNode m)
    (hp : fkIsingSquareRadialPatchPrimalBoundary m p) :
    fkIsingSquareRadialPatchPrimalDirichlet n m hn hm hmpos base p =
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p := by
  letI : Nonempty (FKIsingSquareRadialPatchPrimalNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨0, hmpos⟩), by simp⟩⟩
  exact (Classical.choose_spec (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalGraph_reachable_boundary n m hm)
    (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base))).2 p hp


end
end StatMech.Universality
