/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorScales.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorNeighborhood
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorScales


namespace StatMech.FrontierA

open scoped BigOperators

noncomputable def KWSmallAdaptiveConnectorScales.toPatchedData
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    {r : ℝ} (scales : KWSmallAdaptiveConnectorScales polygon r)
    (hM : 2 ≤ M) : KWAdaptivePatchedData (M := M) polygon where
  data := kwEndpointParameterData polygon M scales.beta scales.alpha
    (by omega) scales.hbeta scales.halpha scales.hsum
  beta := scales.beta
  alpha := scales.alpha
  hM := hM
  hbeta := scales.hbeta
  halpha := scales.halpha
  hsum := scales.hsum
  parameter_one := kwEndpointParameterData_parameter_one
    polygon scales.beta scales.alpha (by omega) scales.hbeta
      scales.halpha scales.hsum
  parameter_penultimate := kwEndpointParameterData_parameter_penultimate
    polygon scales.beta scales.alpha (by omega) scales.hbeta
      scales.halpha scales.hsum
  connector := scales.connector

end StatMech.FrontierA
