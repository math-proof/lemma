/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

def fkIsingSquareInteriorRadialBondMate (n : Nat) (hn : 0 < n)
    (d : FKIsingSquareInteriorRadialDart n) :
    FKIsingSquareInteriorRadialDart n := by
  refine ⟨fkIsingSquareWiredBondMate n hn d.1, ?_⟩
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d.1 d.2,
    fkIsingSquareWedgeFaceKey_bondMate n hn d.1 d.2]
  exact d.2

end
end StatMech.Universality
