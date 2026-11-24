module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part5


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

abbrev FKIsingSquareInteriorRadialCell (n : Nat) :=
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n) //
    ∀ s : FKIsingMedialSide,
      fkIsingSquareInteriorFaceKey n
        (fkIsingSquareWedgeFaceKey n (e, s))}

end
end StatMech.Universality
