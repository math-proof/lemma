/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry.Part4


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def isingFermionicProjectionPolynomialSide (k : Nat) : Nat :=
  isingFermionicPolynomialSide (k + 1)

noncomputable def isingFermionicProjectionPolynomialMesh (k : Nat) : Real :=
  isingFermionicPolynomialMesh (k + 1)

def isingFermionicProjectionPolynomialRadius (k : Nat) : Nat :=
  isingFermionicPolynomialRadius (k + 1)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
