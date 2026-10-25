/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalGhostEnergy


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

def shiftedCoordinate (n i j : Nat) : Int × Int :=
  ((i : Int) - 2 * (n : Int), (j : Int) - 2 * (n : Int))

def coordinateIndex (n : Nat) (q : Int × Int) : Nat × Nat :=
  ((q.1 + 2 * (n : Int)).toNat, (q.2 + 2 * (n : Int)).toNat)

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
