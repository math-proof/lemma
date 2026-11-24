module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2


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

def fkIsingSquareWiredUnitDiagonalStep : Fin 4 → Int × Int :=
  ![(-1, -1), (-1, 1), (1, -1), (1, 1)]


def fkIsingSquareWiredUnitDiagonalReverse : Fin 4 → Fin 4 :=
  ![3, 2, 1, 0]

end
end StatMech.Universality
