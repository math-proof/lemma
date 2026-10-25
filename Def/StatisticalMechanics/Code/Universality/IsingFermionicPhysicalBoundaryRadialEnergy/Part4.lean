/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part26
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (c : FKIsingSquareRadialPatchInteriorCell m) : Real :=
  |fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
        ⟨c.1.1 + 1, by omega⟩ ⟨c.2.1 + 1, by omega⟩ -
      fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
        ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩| +
    |fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
        ⟨c.1.1 + 1, by omega⟩ ⟨c.2.1, by omega⟩ -
      fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
        ⟨c.1.1, by omega⟩ ⟨c.2.1 + 1, by omega⟩|

end
end StatMech.Universality
