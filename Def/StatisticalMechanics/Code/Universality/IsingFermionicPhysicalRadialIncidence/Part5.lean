/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

def fkIsingSquareInteriorRadialCellIncidence
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialCell n) (s : FKIsingMedialSide) :
    FKIsingSquareInteriorRadialIncidence n hn :=
  Quot.mk _ (⟨(e.1, s), e.2 s⟩ : FKIsingSquareInteriorRadialDart n)


end
end StatMech.Universality
