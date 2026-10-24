/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CheckInhomogeneousCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF

#print axioms StatMech.FrontierB.tsum_inhomogeneousFiniteParityKernel
#print axioms StatMech.FrontierB.inhomogeneousFiniteParityPMF_apply
#print axioms StatMech.FrontierB.bind_inhomogeneousFiniteParityPMF_apply
#print axioms StatMech.FrontierB.tsum_inhomogeneousParityCurrentKernel
#print axioms StatMech.FrontierB.inhomogeneousParityCurrentPMF_apply
#print axioms StatMech.FrontierB.inhomogeneousParityCurrentKernel_eq_zero_of_support_ne
#print axioms StatMech.FrontierB.fixedParity_weight_tsum_inhomogeneous
#print axioms StatMech.FrontierB.weight_eq_inhomogeneousParityFiberMass_mul_kernel
