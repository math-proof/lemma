/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CheckPeriodicPlanarSheffieldDeepConnectorMeasureClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorMeasureClosure.Part2
open StatMech FK
open StatMech.FK.PeriodicPlanar

#print axioms measure_eq_zero_of_disjoint_measureReal_tendsto_one
#print axioms
  PeriodicPlanarDualPair.dual_boundaryBand_measure_eq_zero_of_finiteDeepConnector_tendsto_one
#print axioms
  PeriodicPlanarDualPair.complementaryDual_rightHalfPlane_measure_eq_zero_of_finiteDeepConnector_schedules


