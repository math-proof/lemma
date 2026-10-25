/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CheckPeriodicPlanarSheffieldHalfPlaneTopologyClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTopologyClosure
open StatMech FK
open StatMech.FK.PeriodicPlanar

#print axioms
  PeriodicPlanarDualPair.threeCrossingCageEvent_disjoint_boundaryBandHasInfiniteCluster
#print axioms
  PeriodicPlanarDualPair.finiteJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage


