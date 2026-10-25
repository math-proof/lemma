/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCheckerboard.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareRadialPatchDualDirichlet
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (base : Real) : FKIsingSquareRadialPatchDualNode m → Real := by
  have hmpos : 0 < m := by omega
  letI : Nonempty (FKIsingSquareRadialPatchDualNode m) :=
    ⟨⟨(⟨0, hmpos⟩, ⟨1, by omega⟩), by norm_num⟩⟩
  exact Classical.choose (isingFiniteGraph_exists_harmonic_extension
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualGraph_reachable_boundary m)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base))

end
end StatMech.Universality
