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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

noncomputable def radialPatchBase
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) : Real :=
  fkIsingSquareRadialPatchFullValue n m hm hm2
    (vertexPrimitive n hn) (facePrimitive n hn)
    ⟨0, by omega⟩ ⟨0, by omega⟩

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
