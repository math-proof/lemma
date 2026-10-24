/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckIsingSurfaceTensionFiniteInfiniteGap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteInfiniteGap

#print axioms
  StatMech.FrontierA.cubicalSquareWilsonExpectation_le_fixedLoopSequence_self
#print axioms StatMech.FrontierA.cubicalSquareWilsonExpectation_le_infiniteVolume
#print axioms
  StatMech.FrontierA.cubicalInfiniteVolumeSquareWilsonDensity_le_finite
#print axioms StatMech.FrontierA.cubicalFiniteInfiniteSquareDensityGap_nonneg
#print axioms
  StatMech.FrontierA.cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension
#print axioms
  StatMech.FrontierA.rectangularIsingSurfaceTension_eq_zero_iff_gap_tendsto_zero
