module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

def fkIsingSquareInteriorRadialBondPerm (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingSquareInteriorRadialDart n) where
  toFun := fkIsingSquareInteriorRadialBondMate n hn
  invFun := fkIsingSquareInteriorRadialBondMate n hn
  left_inv := fkIsingSquareInteriorRadialBondMate_involutive n hn
  right_inv := fkIsingSquareInteriorRadialBondMate_involutive n hn

end
end StatMech.Universality
