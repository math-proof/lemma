/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part4


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredBoundaryMedialObservable
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) : Complex :=
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
    (.dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterRetainedSide side))


noncomputable def isingFermionicBoundaryVertexNormSqFactor : Real :=
  2 * Real.sqrt 2 / (1 + Real.sqrt 2)

end
end StatMech.Universality
