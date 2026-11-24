module
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
public import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
public import Def.StatisticalMechanics.Code.Exact3D.BoxPathWitness
open Filter


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

open StatMech.Lattice


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical_of_local
    (hlocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical := by
  intro β hβpos _hβc
  exact Filter.Eventually.of_forall fun n => by
    intro v w hvwedge hlt hypos hcoords
    exact hlocal hβpos hvwedge hlt hypos hcoords

end Exact3D
end StatMech
