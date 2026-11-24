module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part6
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive.Part3
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalGhostEnergy
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

noncomputable def coordinatePrimitive
    (n : Nat) (hn : 0 < n) (q : Int × Int) : Real :=
  primitiveNat n hn (coordinateIndex n q).1 (coordinateIndex n q).2

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
