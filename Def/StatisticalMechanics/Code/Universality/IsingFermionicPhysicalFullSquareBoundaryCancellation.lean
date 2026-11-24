module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquarePerimeterDirection :
    FKIsingSquareBoundarySide → FKIsingSquareDirection
  | .bottom => .east
  | .right => .north
  | .top => .west
  | .left => .south

end
end StatMech.Universality
