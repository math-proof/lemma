module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part4


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

def fkIsingSquareInteriorRadialPrimalCoordinate
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) : Int × Int :=
  let u := fkIsingSquareInteriorRadialEndpoint n hn e
  (u.1 0 + u.1 1, u.1 0 - u.1 1)


def fkIsingSquareInteriorRadialFaceCoordinate
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) : Int × Int :=
  let p := fkIsingSquareInteriorRadialFaceKey n hn e
  (p.1 + p.2 + 1, p.1 - p.2)


end
end StatMech.Universality
