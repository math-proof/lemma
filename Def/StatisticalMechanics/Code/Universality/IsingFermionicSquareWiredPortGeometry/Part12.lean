module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part11


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

def fkIsingSquareWiredExpandedStart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareWiredExpandedCarrier n :=
  .inl (fkIsingSquareLeftVerticalLower n hn k, 4)

def fkIsingSquareWiredExpandedMiddle
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareWiredExpandedCarrier n :=
  .inl (fkIsingSquareLeftVerticalUpper n hn k, 6)

def fkIsingSquareWiredExpandedEnd
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareWiredExpandedCarrier n :=
  .inl (fkIsingSquareLeftVerticalUpper n hn k, 7)


end
end StatMech.Universality
