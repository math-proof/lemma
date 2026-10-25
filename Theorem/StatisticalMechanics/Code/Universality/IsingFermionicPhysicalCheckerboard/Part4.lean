/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCheckerboard.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchDualDirichlet_harmonicOn
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real) :
    IsingFiniteGraphHarmonicOn
      (fkIsingSquareRadialPatchDualGraph m)
      (fkIsingSquareRadialPatchDualBoundary m)
      (fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base) := by
  have hmpos : 0 < m := by omega
  letI : Nonempty (FKIsingSquareRadialPatchDualNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨1, by omega⟩), by norm_num⟩⟩
  exact (Classical.choose_spec (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualGraph_reachable_boundary m)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base))).1

theorem fkIsingSquareRadialPatchDualDirichlet_boundary
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real) (p : FKIsingSquareRadialPatchDualNode m)
    (hp : fkIsingSquareRadialPatchDualBoundary m p) :
    fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base p =
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p := by
  have hmpos : 0 < m := by omega
  letI : Nonempty (FKIsingSquareRadialPatchDualNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨1, by omega⟩), by norm_num⟩⟩
  exact (Classical.choose_spec (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualGraph_reachable_boundary m)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base))).2 p hp


theorem fkIsingSquareRadialPatch_constructed_dirichlet_sandwich
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real) :
    (∀ p, fkIsingSquareRadialPatchPrimalDirichlet
        n m hn hm (by omega) base p ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p) ∧
      (∀ p, fkIsingSquareRadialPatchDualValue
          n m hn hm (by omega) base p ≤
        fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base p) := by
  apply fkIsingSquareRadialPatch_checkerboard_dirichlet_sandwich
    n m hn hm (by omega) base
    (fkIsingSquareRadialPatchPrimalDirichlet n m hn hm (by omega) base)
    (fkIsingSquareRadialPatchDualDirichlet n m hn hm hm2 base)
    (fkIsingSquareRadialPatchPrimalDirichlet_harmonicOn
      n m hn hm (by omega) base)
    (fkIsingSquareRadialPatchDualDirichlet_harmonicOn
      n m hn hm hm2 base)
  · exact fkIsingSquareRadialPatchPrimalDirichlet_boundary
      n m hn hm (by omega) base
  · exact fkIsingSquareRadialPatchDualDirichlet_boundary
      n m hn hm hm2 base

end
end StatMech.Universality
