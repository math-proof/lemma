/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckIsingSpinQuantitativeTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSpinQuantitativeTransport

open StatMech.FrontierA

#print axioms SpinConformalTransportEstimate.tendsto_discreteDerivative
#print axioms SpinConformalTransportEstimate.tendsto_spinDerivativeFactor
#print axioms SpinConformalTransportEstimate.correlation_residual_tendsto
#print axioms SpinConformalTransportEstimate.target_tendsto
#print axioms SpinConformalTransportEstimate.target_tendsto_comp
#print axioms
  tendsto_squareBoxRenormalizedSpinCorrelation_of_quantitative_transport
