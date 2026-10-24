/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckIsingSurfaceTensionLebowitzPfisterLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionLebowitzPfisterLower

#print axioms StatMech.FrontierA.hasDerivAt_standardCubicInterfaceDensity
#print axioms
  StatMech.FrontierA.standardCubicInterfaceDensity_deriv_ge_two_mul_sq_of_energyDeficit
#print axioms
  StatMech.FrontierA.standardCubicInterfaceDensity_deriv_ge_two_mul_magnetization_sq
#print axioms
  StatMech.FrontierA.standardCubicInterfaceDensity_hasWeakLowerBound_of_energyDeficit
#print axioms
  StatMech.FrontierA.rectangularIsingSurfaceTension_pos_iff_ordered_of_finite_energy_deficit
