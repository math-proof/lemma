/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CheckPeriodicPlanarSheffieldDeepConnectorRows.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorRows.Part2
open StatMech.FK.PeriodicPlanar
open PeriodicPlanarDualPair

#print axioms
  PeriodicPlaneEmbedding.exists_separated_finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_gt
#print axioms finiteDeepConnectorBandSchedule_of_separatedRows
#print axioms complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows


