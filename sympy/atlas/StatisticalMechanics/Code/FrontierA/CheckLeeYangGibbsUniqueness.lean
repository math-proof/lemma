/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckLeeYangGibbsUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.LeeYangGibbsUniqueness

#print axioms StatMech.FrontierA.fvBoxPressure_hasDerivAt_field
#print axioms StatMech.FrontierA.plusBoxAverageSpin_tendsto_pressureDeriv
#print axioms StatMech.FrontierA.minusBoxAverageSpin_tendsto_pressureDeriv
#print axioms StatMech.FrontierA.plusState_eq_minusState_of_positive_field
#print axioms StatMech.FrontierA.isDLRState_map_flipConfig
#print axioms StatMech.FrontierA.gibbs_unique_of_nonzero_field_of_pos_beta
#print axioms StatMech.FrontierA.plusState_eq_minusState_of_nonzero_field
#print axioms StatMech.FrontierA.gibbs_unique_of_nonzero_field
