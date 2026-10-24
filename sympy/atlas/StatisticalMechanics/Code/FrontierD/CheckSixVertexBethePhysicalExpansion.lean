/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/CheckSixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion

open StatMech.FrontierD

#print axioms StatMech.FrontierD.sixVertexBethe_geometricInterval_int
#print axioms
  StatMech.FrontierD.sixVertexBetheCollisionFreeIntervalSum_eq_words
#print axioms
  StatMech.FrontierD.sixVertexBetheRawIEWordCoefficient_eq_wordCoefficient
#print axioms
  StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.physicalCyclicIntervalExpansion
#print axioms
  StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.physicalWordExpansion
#print axioms
  SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation
