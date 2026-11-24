module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/
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

noncomputable def fkIsingSquareWiredFullInteriorCycle
    (n : Nat) (hn : 0 < n) :
    FKIsingSquareInteriorCell n →
      StatMech.FrontierA.PermCycleClass
        (fkIsingSquareWiredBlackBoundaryPerm n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)) :=
  fun c ↦ Quot.mk _ (fkIsingSquareInteriorCellBlack n c)

end
end StatMech.Universality
