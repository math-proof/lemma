/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckQuantumIsingLieTrotter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingLieTrotter

#print axioms StatMech.FrontierA.quantumIsingTrotterStep_scaled_error_norm_tendsto
#print axioms StatMech.FrontierA.quantumIsingExponentialStep_scaled_error_norm_tendsto
#print axioms StatMech.FrontierA.quantumIsingTrotterStep_power_tendsto_exp
#print axioms StatMech.FrontierA.quantumIsingTrotterTransferMatrix_power_tendsto_exp
#print axioms StatMech.FrontierA.quantumIsingTrotterTrace_tendsto_quantumPartition
#print axioms StatMech.FrontierA.quantumIsingNormalizedClassicalCylinder_tendsto_quantumPartition
