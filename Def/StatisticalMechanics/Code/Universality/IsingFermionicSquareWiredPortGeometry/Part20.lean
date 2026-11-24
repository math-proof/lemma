module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part18


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

noncomputable def fkIsingSquareWiredDartPhysicalBlackEquiv (n : Nat) :
    FKIsingMedialDart (fkSquareBoxPlanar n) ≃
      FKIsingSquareWiredPhysicalBlackCarrier n :=
  Equiv.ofBijective (fkIsingSquareWiredPhysicalBlackOfDart n)
    (fkIsingSquareWiredPhysicalBlackOfDart_bijective n)


noncomputable def fkIsingSquareWiredPhysicalBlackPortIntPosition (n : Nat) :
    FKIsingSquareWiredPhysicalBlackCarrier n → Int × Int :=
  fkIsingSquareWiredPortIntPosition n ∘
    (fkIsingSquareWiredDartPhysicalBlackEquiv n).symm

end
end StatMech.Universality
