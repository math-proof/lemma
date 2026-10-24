/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/CheckSixVertexBetheKernelQuadrature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheKernelQuadrature

#print axioms StatMech.FrontierD.sixVertexRootDensityWeight_lipschitz
#print axioms StatMech.FrontierD.sixVertexRootDensityKernel_lipschitz_right
#print axioms StatMech.FrontierD.abs_kernel_mul_finiteDensity_cellMass_sub_integral_le
#print axioms StatMech.FrontierD.abs_kernel_div_width_sub_finiteDensity_cellIntegral_le
#print axioms StatMech.FrontierD.abs_kernel_div_width_sub_finiteDensity_rightCellIntegral_le
#print axioms StatMech.FrontierD.abs_kernel_div_width_sub_finiteDensity_boundaryIntegral_le
