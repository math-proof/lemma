module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    fkIsingSquareWiredBondArcLength n u d = 1 ∨
      fkIsingSquareWiredBondArcLength n u d = 3 ∨
      fkIsingSquareWiredBondArcLength n u d = 5 := by
  classical
  cases d <;>
    simp only [fkIsingSquareWiredBondArcLength] <;>
    split_ifs <;> simp


theorem fkIsingSquareWiredPortSlot_nextDirection
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    fkIsingSquareWiredPortSlot
        (fkIsingSquareNextDirection n u d) .clockwise =
      fkIsingSquareWiredPortSlot d .counterclockwise +
        fkIsingSquareWiredBondArcLength n u d := by
  classical
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp [fkIsingSquareNextDirection, fkIsingSquareWiredBondArcLength,
      he, hnorth, hw, hs, fkIsingSquareWiredPortSlot]


end
end StatMech.Universality
