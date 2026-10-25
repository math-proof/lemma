/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareInteriorRadialBondMate_ne
    (n : Nat) (hn : 0 < n)
    (d : FKIsingSquareInteriorRadialDart n) :
    fkIsingSquareInteriorRadialBondMate n hn d ≠ d := by
  intro h
  have hval := congrArg Subtype.val h
  exact fkIsingSquareWiredBondMate_ne n hn d.1 hval


end
end StatMech.Universality
