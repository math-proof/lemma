module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialReachability
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonReduction
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
public import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialClusterBoundary
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClusterBoundary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectMedialDartPrimalLabel_dartAtPrimalVertex
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectMedialDartPrimalLabel R
      (fkRectMedialDartAtPrimalVertex R x) = x := by
  by_cases hx : Even x.2.val <;>
    simp [fkRectMedialDartAtPrimalVertex,
      fkRectMedialDartPrimalLabel_west_vertexOfEdge,
      fkRectMedialDartPrimalLabel_east_vertexOfEdge,
      fkRectMedialWestPrimal, fkRectMedialEastPrimal, hx]


end
end StatMech.FrontierD
