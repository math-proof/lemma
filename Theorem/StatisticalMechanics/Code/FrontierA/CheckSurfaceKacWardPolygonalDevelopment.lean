/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckSurfaceKacWardPolygonalDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3


namespace StatMech.FrontierA

#print axioms
  ClosedPolygonalFlatSurfaceGraphAtlas.exists_developedPolygon_odd_winding
#print axioms
  ClosedPolygonalFlatSurfaceGraphAtlas.developedPolygon_winding_eq_two_mul_half_add_one
#print axioms ClosedPolygonalFlatSurfaceGraphAtlas.developedGaussBonnet
#print axioms
  ClosedPolygonalFlatSurfaceGraphAtlas.toClosedMetricFlatSurfaceGraphAtlas
#print axioms ClosedPolygonalFlatSurfaceGraphAtlas.kacWard_arf_formula

end StatMech.FrontierA
