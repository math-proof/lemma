/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part5


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareWiredBoundaryVertexSquareRepresentative
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) : Complex :=
  (Real.sqrt isingFermionicBoundaryVertexNormSqFactor : Complex) *
    fkIsingSquareWiredBoundaryMedialObservable n hn side k

end
end StatMech.Universality
