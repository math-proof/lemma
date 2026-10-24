/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckIsoradialKacWardLaplacianMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianMetricClosure

namespace StatMech.FrontierA

#print axioms
  IsoradialMetricComponentOrientationData.toComponentIdentification
#print axioms
  MetricCriticalIsoradialGenusZeroOneEmbedding.toCriticalIsoradialGenusZeroOneEmbedding
#print axioms
  MetricCriticalIsoradialGenusZeroOneEmbedding.det_eq_laplacian

end StatMech.FrontierA
