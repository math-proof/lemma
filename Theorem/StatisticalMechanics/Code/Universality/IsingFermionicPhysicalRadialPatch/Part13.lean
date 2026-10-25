/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part13


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_superharmonicOn_region
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G
      (fun x ↦ ¬ fkIsingSquareRadialPatchInteriorEvenRegion n m hm x)
      (fkIsingSquareRadialPatchPrimalPrimitiveExtension
        n m hn hm hmpos base) := by
  intro x hx
  have hregion : fkIsingSquareRadialPatchInteriorEvenRegion n m hm x := by
    exact Classical.byContradiction (fun h ↦ hx h)
  rcases hregion with ⟨i, j, hi0, hi1, hj0, hj1, heven, rfl⟩
  exact fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonpos
    n m i.1 j.1 hn hm hmpos base hi0 hi1 hj0 hj1 heven


end
end StatMech.Universality
