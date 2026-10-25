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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

noncomputable def vertexPrimitive
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n) : Real :=
  coordinatePrimitive n hn (fkIsingSquareFullVertexCoordinate n x) -
    coordinatePrimitive n hn
      (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))

noncomputable def facePrimitive
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) : Real :=
  coordinatePrimitive n hn (fkIsingSquareFullFaceCoordinate n c) -
    coordinatePrimitive n hn
      (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
